{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

import Control.Logger.Simple
import Control.Monad (forM_, void)
import Control.Monad.Except (runExceptT)
import qualified Data.Aeson as J
import Data.String (fromString)
import qualified Network.Socket as N
import qualified Simplex.Messaging.Crypto as C
import Simplex.Messaging.Encoding.String (strDecode, strEncode)
import Simplex.Messaging.Transport (TLS (..), cGet, cPut)
import Simplex.Messaging.Transport.Client (TransportHost (..))
import Simplex.RemoteControl.Client
import Simplex.RemoteControl.Invitation
import Simplex.RemoteControl.Types
import System.Environment (lookupEnv)
import Test.Hspec
import UnliftIO

main :: IO ()
main = withGlobalLogging (LogConfig Nothing True) $ hspec $ do
  describe "owned XRCP listener" $ do
    it "reconnects with fresh keys, rejects another phone and ignores stale release" $ do
      drg <- C.newRandom
      pairing <- newRCHostPairing drg
      endpoint <- lookupEnv "XRCP_TEST_ADDRESS"
      let addr = maybe (RCCtrlAddress (THIPv4 (127, 0, 0, 1)) "lo") (\ip -> RCCtrlAddress (either error id $ strDecode $ fromString ip) "tailscale0") endpoint
      (_, signed, host, incoming) <- right =<< runExceptT (connectRCHostPersistent drg pairing J.Null False (Just addr) Nothing)
      inv <- maybe (fail "signature") pure $ verifySignedInvitation signed
      let connect cp = do
            (client, steps) <- right =<< runExceptT (connectRCCtrl drg inv cp J.Null)
            (sid, _, confirmed) <- step steps
            confirmCtrlSession client True
            (session, cp') <- step confirmed
            (hsid, _, hc) <- step incoming
            (RCHostSession {tls = hostTLS}, _, hp') <- step hc
            sid `shouldBe` hsid
            pure (client, session, cp', hp', sid, hostTLS)
      flip finally (cancelHostClient host) $ do
        (client1, _, cp1, _, sid1, _) <- connect Nothing
        cancelCtrlClient client1
        releaseHostSession host sid1
        -- The very first QR session must update the live listener's TLS pin.
        (stranger, badSteps) <- right =<< runExceptT (connectRCCtrl drg inv Nothing J.Null)
        timeout 3000000 (atomically $ takeTMVar badSteps) >>= (\r -> rejected r `shouldBe` True)
        cancelCtrlClient stranger
        (client2, RCCtrlSession {tls = mobileTLS}, cp2, _, sid2, hostTLS) <- connect (Just cp1)
        C.publicKey (dhPrivKey cp1) `shouldNotBe` C.publicKey (dhPrivKey cp2)
        sid1 `shouldNotBe` sid2
        timeout 1000000 (releaseHostSession host sid1) `shouldReturn` Just ()
        cPut mobileTLS "alive"
        timeout 1000000 (cGet hostTLS 5) `shouldReturn` Just "alive"
        -- Present the real pinned CA certificate with an unrelated signing key.
        (_, fakeKey) <- atomically $ C.generateSignatureKeyPair C.SEd25519 drg
        releaseHostSession host sid2
        cancelCtrlClient client2
        (forged, forgedSteps) <- right =<< runExceptT (connectRCCtrl drg inv (Just (cp2 :: RCCtrlPairing) {caKey = fakeKey}) J.Null)
        timeout 3000000 (atomically $ takeTMVar forgedSteps) >>= (\r -> rejected r `shouldBe` True)
        cancelCtrlClient forged
        -- Loss during confirmation must also release the admitted handler.
        (pending, pendingSteps) <- right =<< runExceptT (connectRCCtrl drg inv (Just cp2) J.Null)
        _ <- step pendingSteps
        (pendingSid, _, _) <- step incoming
        timeout 1000000 (releaseHostSession host pendingSid) `shouldReturn` Just ()
        cancelCtrlClient pending
        cancelCtrlClient pending
        forM_ [1 .. 8 :: Int] $ \_ -> do
          (client, _, _, _, sid, _) <- connect (Just cp2)
          releaseHostSession host sid
          releaseHostSession host sid
          cancelCtrlClient client
    it "fetches fresh invitations after listener restart with mutual identity checks" $ do
      drg <- C.newRandom
      pairing <- newRCHostPairing drg
      let addr = RCCtrlAddress (THIPv4 (127, 0, 0, 1)) "lo"
      (_, signed1@RCSignedInvitation {invitation = oldInv@RCInvitation {port}}, listener1, steps1) <- right =<< runExceptT (connectRCHostPersistent drg pairing J.Null False (Just addr) Nothing)
      inv1 <- maybe (fail "signature") pure $ verifySignedInvitation signed1
      (phone1, phoneSteps1) <- right =<< runExceptT (connectRCCtrl drg inv1 Nothing J.Null)
      (_, _, confirmation1) <- step phoneSteps1
      confirmCtrlSession phone1 True
      (_, cp1) <- step confirmation1
      (sid1, _, confirmed1) <- step steps1
      (_, _, hp1) <- step confirmed1
      releaseHostSession listener1 sid1
      cancelCtrlClient phone1
      cancelHostClient listener1
      (_, signed2@RCSignedInvitation {invitation = freshInv}, listener2, steps2) <- right =<< runExceptT (connectRCHostPersistent drg hp1 J.Null False (Just addr) (Just port))
      flip finally (cancelHostClient listener2) $ do
        dh oldInv `shouldNotBe` dh freshInv
        skey oldInv `shouldNotBe` skey freshInv
        let RCCtrlPairing {idPubKey = desktopId} = cp1
            fetch cp = runExceptT (requestRCCtrlInvitation drg cp (THIPv4 (127, 0, 0, 1)) port) `catchAny` (pure . Left . RCEException . show)
        -- A correct TLS pin with the wrong long-term signing identity fails.
        (wrongIdentity, _) <- atomically $ C.generateKeyPair drg
        fetch cp1 {idPubKey = wrongIdentity} >>= (\r -> either (== RCEIdentity) (const False) r `shouldBe` True)
        -- A different phone CA (even with correct desktop pins) is rejected.
        (_, otherSigned, otherListener, _) <- right =<< runExceptT (connectRCHostPersistent drg pairing J.Null False (Just addr) Nothing)
        otherInv <- maybe (fail "signature") pure $ verifySignedInvitation otherSigned
        (otherPhone, otherSteps) <- right =<< runExceptT (connectRCCtrl drg otherInv Nothing J.Null)
        (_, _, otherConfirmation) <- step otherSteps
        confirmCtrlSession otherPhone True
        (_, otherPairing) <- step otherConfirmation
        cancelCtrlClient otherPhone
        cancelHostClient otherListener
        fetch otherPairing {ctrlFingerprint = ctrlFingerprint cp1, idPubKey = desktopId} >>= (\r -> either (const True) (const False) r `shouldBe` True)
        -- Same CA certificate with an unrelated CA signing key is not identity.
        (_, fakeCAKey) <- atomically $ C.generateSignatureKeyPair C.SEd25519 drg
        fetch cp1 {caKey = fakeCAKey} >>= (\r -> either (const True) (const False) r `shouldBe` True)
        RCVerifiedInvitation fetched <- right =<< fetch cp1
        strEncode fetched `shouldBe` strEncode freshInv
        RCVerifiedInvitation viaDNS <- right =<< runExceptT (requestRCCtrlInvitation drg cp1 (THDomainName "localhost") port)
        strEncode viaDNS `shouldBe` strEncode freshInv
        -- Fetch does not publish a fake application session or seize admission.
        atomically (isEmptyTMVar steps2) `shouldReturn` True
        -- Replaying the old invitation cannot establish the restarted session.
        (stalePhone, staleSteps) <- right =<< runExceptT (connectRCCtrl drg inv1 (Just cp1) J.Null)
        (_, _, staleConfirmation) <- step staleSteps
        void $ timeout 100000 (confirmCtrlSession stalePhone True)
        (staleSid, _, staleHostSteps) <- step steps2
        timeout 3000000 (atomically $ takeTMVar staleHostSteps) >>= (\r -> rejected r `shouldBe` True)
        cancelCtrlClient stalePhone
        releaseHostSession listener2 staleSid
        inv2 <- maybe (fail "signature") pure $ verifySignedInvitation signed2
        (phone2, phoneSteps2) <- right =<< runExceptT (connectRCCtrl drg inv2 (Just cp1) J.Null)
        (sid2, phoneTLS, confirmation2) <- step phoneSteps2
        confirmCtrlSession phone2 True
        (_, cp2) <- step confirmation2
        (_, hostTLS, confirmed2) <- step steps2
        _ <- step confirmed2
        sid1 `shouldNotBe` sid2
        C.publicKey (dhPrivKey cp1) `shouldNotBe` C.publicKey (dhPrivKey cp2)
        cPut phoneTLS "fresh"
        timeout 1000000 (cGet hostTLS 5) `shouldReturn` Just "fresh"
        cancelCtrlClient phone2
    it "closes the listening port when its owner stops" $ do
      drg <- C.newRandom
      pairing <- newRCHostPairing drg
      (_, RCSignedInvitation {invitation = RCInvitation {port}}, host, _) <- right =<< runExceptT (connectRCHostPersistent drg pairing J.Null False (Just $ RCCtrlAddress (THIPv4 (127, 0, 0, 1)) "lo") Nothing)
      cancelHostClient host
      bracket (N.socket N.AF_INET N.Stream N.defaultProtocol) N.close $ \sock ->
        tryIO (N.connect sock $ N.SockAddrInet (fromIntegral port) $ N.tupleToHostAddress (127, 0, 0, 1)) >>= (`shouldSatisfy` either (const True) (const False))
    it "reports an occupied port without leaking a waiting startup" $ do
      drg <- C.newRandom
      pairing <- newRCHostPairing drg
      bracket (N.socket N.AF_INET N.Stream N.defaultProtocol) N.close $ \sock -> do
        N.bind sock $ N.SockAddrInet 0 $ N.tupleToHostAddress (127, 0, 0, 1)
        N.listen sock 1
        port <- N.socketPort sock
        result <- timeout 2000000 $ runExceptT $ connectRCHostPersistent drg pairing J.Null False (Just $ RCCtrlAddress (THIPv4 (127, 0, 0, 1)) "lo") (Just $ fromIntegral port)
        (case result of Just (Left RCETLSStartFailed) -> True; _ -> False) `shouldBe` True
    it "fails closed when the selected interface is absent" $ do
      drg <- C.newRandom
      pairing <- newRCHostPairing drg
      result <- runExceptT $ connectRCHostPersistent drg pairing J.Null False (Just $ RCCtrlAddress (THIPv4 (100, 100, 100, 100)) "absent-tailscale") Nothing
      either (== RCENoLocalAddress) (const False) result `shouldBe` True
  where
    rejected (Just (Left _)) = True
    rejected _ = False

right :: Show e => Either e a -> IO a
right = either (fail . show) pure

step :: Show e => TMVar (Either e a) -> IO a
step v = timeout 5000000 (atomically $ takeTMVar v) >>= maybe (fail "handshake timeout") right
