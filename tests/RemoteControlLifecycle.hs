{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

import Control.Monad (forM_)
import Control.Logger.Simple
import Control.Monad.Except (runExceptT)
import qualified Data.Aeson as J
import qualified Network.Socket as N
import Data.String (fromString)
import qualified Simplex.Messaging.Crypto as C
import Simplex.Messaging.Transport (TLS (..), cPut, cGet)
import Simplex.Messaging.Encoding.String (strDecode)
import System.Environment (lookupEnv)
import Simplex.Messaging.Transport.Client (TransportHost (..))
import Simplex.RemoteControl.Client
import Simplex.RemoteControl.Invitation
import Simplex.RemoteControl.Types
import Test.Hspec
import UnliftIO

main :: IO ()
main = withGlobalLogging (LogConfig Nothing True) $ hspec $ do
  describe "owned XRCP listener" $ do
    it "reconnects with fresh keys, rejects another phone and ignores stale release" $ do
      drg <- C.newRandom
      pairing <- newRCHostPairing drg
      endpoint <- lookupEnv "XRCP_TEST_ADDRESS"
      let addr = maybe (RCCtrlAddress (THIPv4 (127,0,0,1)) "lo") (\ip -> RCCtrlAddress (either error id $ strDecode $ fromString ip) "tailscale0") endpoint
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
        forM_ [1..8 :: Int] $ \_ -> do
          (client, _, _, _, sid, _) <- connect (Just cp2)
          releaseHostSession host sid
          releaseHostSession host sid
          cancelCtrlClient client
    it "closes the listening port when its owner stops" $ do
      drg <- C.newRandom
      pairing <- newRCHostPairing drg
      (_, RCSignedInvitation {invitation = RCInvitation {port}}, host, _) <- right =<< runExceptT (connectRCHostPersistent drg pairing J.Null False (Just $ RCCtrlAddress (THIPv4 (127,0,0,1)) "lo") Nothing)
      cancelHostClient host
      bracket (N.socket N.AF_INET N.Stream N.defaultProtocol) N.close $ \sock ->
        tryIO (N.connect sock $ N.SockAddrInet (fromIntegral port) $ N.tupleToHostAddress (127,0,0,1)) >>= (`shouldSatisfy` either (const True) (const False))
    it "reports an occupied port without leaking a waiting startup" $ do
      drg <- C.newRandom
      pairing <- newRCHostPairing drg
      bracket (N.socket N.AF_INET N.Stream N.defaultProtocol) N.close $ \sock -> do
        N.bind sock $ N.SockAddrInet 0 $ N.tupleToHostAddress (127,0,0,1)
        N.listen sock 1
        port <- N.socketPort sock
        result <- timeout 2000000 $ runExceptT $ connectRCHostPersistent drg pairing J.Null False (Just $ RCCtrlAddress (THIPv4 (127,0,0,1)) "lo") (Just $ fromIntegral port)
        (case result of Just (Left RCETLSStartFailed) -> True; _ -> False) `shouldBe` True
    it "fails closed when the selected interface is absent" $ do
      drg <- C.newRandom
      pairing <- newRCHostPairing drg
      result <- runExceptT $ connectRCHostPersistent drg pairing J.Null False (Just $ RCCtrlAddress (THIPv4 (100,100,100,100)) "absent-tailscale") Nothing
      either (== RCENoLocalAddress) (const False) result `shouldBe` True
  where
    rejected (Just (Left _)) = True
    rejected _ = False

right :: Show e => Either e a -> IO a
right = either (fail . show) pure

step :: Show e => TMVar (Either e a) -> IO a
step v = timeout 5000000 (atomically $ takeTMVar v) >>= maybe (fail "handshake timeout") right
