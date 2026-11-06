{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-warn-ambiguous-fields #-}

module Simplex.RemoteControl.Client
  ( RCHostClient (action),
    RCHostConnection,
    newRCHostPairing,
    connectRCHost,
    connectRCHostPersistent,
    releaseHostSession,
    cancelHostClient,
    RCCtrlClient (action),
    RCCtrlConnection,
    connectRCCtrl,
    requestRCCtrlInvitation,
    discoverRCCtrl,
    confirmCtrlSession,
    cancelCtrlClient,
    RCStepTMVar,
    rcEncryptBody,
    rcDecryptBody,
    xrcpBlockSize,
    -- for tests only
    sendRCPacket,
    receiveRCPacket,
    findRCCtrlPairing,
  ) where

import Control.Applicative ((<|>))
import Control.Logger.Simple
import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Crypto.Random (ChaChaDRG)
import qualified Data.Aeson as J
import Data.Bitraversable (bimapM)
import Data.ByteString (ByteString)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC
import qualified Data.ByteString.Lazy as LB
import Data.Default (def)
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as L
import Data.Maybe (isNothing)
import qualified Data.Text as T
import Data.Time.Clock.System (SystemTime (..), getSystemTime)
import Data.Tuple (swap)
import Data.Word (Word16)
import qualified Data.X509 as X
import Data.X509.Validation (Fingerprint (..), getFingerprint)
import Network.Socket (PortNumber, SockAddr (..), hostAddressToTuple)
import qualified Network.TLS as TLS
import qualified Network.UDP as UDP
import Simplex.Messaging.Agent.Client ()
import qualified Simplex.Messaging.Crypto as C
import Simplex.Messaging.Crypto.Lazy (LazyByteString)
import qualified Simplex.Messaging.Crypto.Lazy as LC
import Simplex.Messaging.Crypto.SNTRUP761
import Simplex.Messaging.Crypto.SNTRUP761.Bindings
import Simplex.Messaging.Encoding
import Simplex.Messaging.Encoding.String (StrEncoding (..))
import Simplex.Messaging.Transport (TSbChainKeys (..), TLS (..), TransportPeer (..), cGet, cPut)
import Simplex.Messaging.Transport.Buffer (peekBuffered)
import Simplex.Messaging.Transport.Client (TransportClientConfig (..), TransportHost (..), defaultTransportClientConfig, runTransportClient)
import Simplex.Messaging.Transport.Credentials (genCredentials, tlsCredentials)
import Simplex.Messaging.Transport.Server (validateClientCertificate)
import Simplex.Messaging.Util
import Simplex.Messaging.Version
import Simplex.RemoteControl.Discovery (getLocalAddress, recvAnnounce, startTLSServerOn, withListener, withSender)
import Simplex.RemoteControl.Invitation
import Simplex.RemoteControl.Types
import UnliftIO
import UnliftIO.Concurrent

xrcpBlockSize :: Int
xrcpBlockSize = 16384

helloBlockSize :: Int
helloBlockSize = 12288

encInvitationSize :: Int
encInvitationSize = 900

newRCHostPairing :: TVar ChaChaDRG -> IO RCHostPairing
newRCHostPairing drg = do
  ((_, caKey), caCert) <- genCredentials drg Nothing (25, 24 * 999999) "ca"
  (_, idPrivKey) <- atomically $ C.generateKeyPair drg
  pure RCHostPairing {caKey, caCert, idPrivKey, knownHost = Nothing}

data RCHostClient = RCHostClient
  { action :: Async (),
    client_ :: RCHClient_
  }

data RCHClient_ = RCHClient_
  { startedPort :: TMVar (Maybe PortNumber),
    announcer :: TMVar (Async (Either RCErrorType ())),
    knownHostVar :: TVar (Maybe KnownHostPairing),
    activeSession :: TMVar (SessionCode, TMVar (), TMVar (), ThreadId)
  }

type RCHostConnection = (NonEmpty RCCtrlAddress, RCSignedInvitation, RCHostClient, RCStepTMVar (SessionCode, TLS 'TServer, RCStepTMVar (RCHostSession, RCHostHello, RCHostPairing)))

connectRCHost :: TVar ChaChaDRG -> RCHostPairing -> J.Value -> Bool -> Maybe RCCtrlAddress -> Maybe Word16 -> ExceptT RCErrorType IO RCHostConnection
connectRCHost = connectRCHost_ False

-- | An owned listener that can accept a new transport after releaseHostSession.
-- Session keys remain memory-only and are never restored after listener restart.
connectRCHostPersistent :: TVar ChaChaDRG -> RCHostPairing -> J.Value -> Bool -> Maybe RCCtrlAddress -> Maybe Word16 -> ExceptT RCErrorType IO RCHostConnection
connectRCHostPersistent = connectRCHost_ True

connectRCHost_ :: Bool -> TVar ChaChaDRG -> RCHostPairing -> J.Value -> Bool -> Maybe RCCtrlAddress -> Maybe Word16 -> ExceptT RCErrorType IO RCHostConnection
connectRCHost_ persistent drg pairing@RCHostPairing {caKey, caCert, idPrivKey, knownHost} ctrlAppInfo multicast rcAddrPrefs_ port_ = do
  when (multicast && isNothing knownHost) $ throwE RCENewController
  r <- newEmptyTMVarIO
  found@(RCCtrlAddress {address, interface = chosenIface} :| _) <- findCtrlAddress
  -- A missing explicitly selected interface must not expose a retained listener
  -- on a different network. The normal LAN API retains its previous behavior.
  when persistent $ forM_ rcAddrPrefs_ $ \RCCtrlAddress {address = wanted, interface = iface} ->
    unless (address == wanted || chosenIface == iface) $ throwE RCENoLocalAddress
  c@RCHClient_ {startedPort, announcer} <- liftIO mkClient
  invitationVar <- newEmptyTMVarIO
  hostKeys <- atomically genHostKeys
  action <- liftIO $ runClient (if persistent && not (isNothing rcAddrPrefs_) then Just $ BC.unpack $ strEncode address else Nothing) c r invitationVar hostKeys
  -- wait for the port to make invitation
  portNum <- atomically $ readTMVar startedPort
  signedInv@RCSignedInvitation {invitation} <- maybe (throwE RCETLSStartFailed) (liftIO . mkInvitation hostKeys address) portNum
  atomically $ putTMVar invitationVar signedInv
  when multicast $ case knownHost of
    Nothing -> throwE RCENewController
    Just KnownHostPairing {hostDhPubKey} -> do
      ann <- liftIO . async . runExceptT $ announceRC drg 60 idPrivKey hostDhPubKey hostKeys invitation
      atomically $ putTMVar announcer ann
  pure (found, signedInv, RCHostClient {action, client_ = c}, r)
  where
    findCtrlAddress :: ExceptT RCErrorType IO (NonEmpty RCCtrlAddress)
    findCtrlAddress = do
      found' <- liftIO $ getLocalAddress rcAddrPrefs_
      maybe (throwE RCENoLocalAddress) pure $ L.nonEmpty found'
    mkClient :: IO RCHClient_
    mkClient = do
      startedPort <- newEmptyTMVarIO
      announcer <- newEmptyTMVarIO
      knownHostVar <- newTVarIO knownHost
      activeSession <- newEmptyTMVarIO
      pure RCHClient_ {startedPort, announcer, knownHostVar, activeSession}
    runClient :: Maybe String -> RCHClient_ -> RCStepTMVar (SessionCode, TLS 'TServer, RCStepTMVar (RCHostSession, RCHostHello, RCHostPairing)) -> TMVar RCSignedInvitation -> RCHostKeys -> IO (Async ())
    runClient bindHost RCHClient_ {startedPort, announcer, knownHostVar, activeSession} r invitationVar hostKeys = do
      tlsCreds <- genTLSCredentials drg caKey caCert
      startTLSServerOn bindHost port_ startedPort tlsCreds (tlsHooks r knownHostVar activeSession) $ \tls ->
        if tlsALPN tls == Just invitationALPN
          then void . timeout 15000000 . runExceptT $ do
            -- Authentication is connection-local. Recheck the live pin after TLS;
            -- an overlapping first pairing must not authorize another certificate.
            kh <- readTVarIO knownHostVar
            case (kh, tlsPeerCert tls) of
              (Just h, X.CertificateChain [_leaf, ca]) | hostFingerprint h == certFingerprint ca -> do
                inv <- atomically $ readTMVar invitationVar
                sendRCPacket tls (Large $ strEncode inv)
              _ -> throwE RCEIdentity
          else acceptSession tls
      where
        acceptSession tls = do
          end <- newEmptyTMVarIO
          finished <- newEmptyTMVarIO
          tid <- myThreadId
          let sid = tlsUniq tls
          acquired <- atomically $ tryPutTMVar activeSession (sid, end, finished, tid)
          when acquired $
            (void . runExceptT $ do
              r' <- newEmptyTMVarIO
              whenM (atomically $ tryPutTMVar r $ Right (sid, tls, r')) $
                runSession tls end r' `putRCError` r')
              `finally` do
                -- Close before releasing admission; old handlers cannot accumulate.
                TLS.contextClose (tlsContext tls) `catchAny` (logError . tshow)
                atomically $ void (tryTakeTMVar activeSession) >> putTMVar finished ()
        runSession tls end r' = do
          -- TLS handshakes may overlap. Recheck the latest pin after admission.
          kh <- readTVarIO knownHostVar
          hostCA <- case tlsPeerCert tls of
            X.CertificateChain [_leaf, ca] -> pure $ certFingerprint ca
            _ -> throwE RCEIdentity
          forM_ kh $ \h -> unless (hostFingerprint h == hostCA) $ throwE RCEIdentity
          hostEncHello <- receiveRCPacket tls
          (ctrlEncHello, sessionKeys, helloBody, pairing') <- prepareHostSession drg hostCA pairing {knownHost = kh} hostKeys hostEncHello
          sendRCPacket tls ctrlEncHello
          -- Pin before publishing success, including the very first QR session.
          let RCHostPairing {knownHost = kh'} = pairing'
          atomically $ writeTVar knownHostVar kh'
          whenM (atomically $ tryPutTMVar r' $ Right (RCHostSession {tls, sessionKeys}, helloBody, pairing')) $ do
            atomically (tryReadTMVar announcer) >>= mapM_ uninterruptibleCancel
            atomically $ takeTMVar end
    tlsHooks :: TMVar a -> TVar (Maybe KnownHostPairing) -> TMVar b -> TLS.ServerHooks
    tlsHooks r knownHostVar activeSession =
      def
        { TLS.onALPNClientSuggest = if persistent then Just (\offered -> pure $ if invitationALPN `elem` offered then invitationALPN else "") else Nothing,
          TLS.onNewHandshake = \_ -> atomically $ (&&) <$> isEmptyTMVar r <*> isEmptyTMVar activeSession,
          TLS.onClientCertificate = \cc@(X.CertificateChain chain) ->
            case chain of
              [_leaf, ca] -> do
                kh <- readTVarIO knownHostVar
                let accept = maybe True (\h -> hostFingerprint h == certFingerprint ca) kh
                if accept
                  then validateClientCertificate cc >>= \case
                    Nothing -> pure TLS.CertificateUsageAccept
                    Just reason -> pure $ TLS.CertificateUsageReject reason
                  else pure $ TLS.CertificateUsageReject TLS.CertificateRejectUnknownCA
              _ -> pure $ TLS.CertificateUsageReject TLS.CertificateRejectUnknownCA
        }
    genHostKeys :: STM RCHostKeys
    genHostKeys = do
      sessKeys <- C.generateKeyPair drg
      dhKeys <- C.generateKeyPair drg
      pure RCHostKeys {sessKeys, dhKeys}
    mkInvitation :: RCHostKeys -> TransportHost -> PortNumber -> IO RCSignedInvitation
    mkInvitation RCHostKeys {sessKeys, dhKeys} host portNum = do
      ts <- getSystemTime
      let inv =
            RCInvitation
              { ca = certFingerprint caCert,
                host,
                port = fromIntegral portNum,
                v = supportedRCPVRange,
                app = ctrlAppInfo,
                ts,
                skey = fst sessKeys,
                idkey = C.publicKey idPrivKey,
                dh = fst dhKeys
              }
      pure $ signInvitation (snd sessKeys) idPrivKey inv

genTLSCredentials :: TVar ChaChaDRG -> C.APrivateSignKey -> X.SignedCertificate -> IO TLS.Credential
genTLSCredentials drg caKey caCert = do
  let caCreds = (C.signatureKeyPair caKey, caCert)
  leaf <- genCredentials drg (Just caCreds) (1, 24 * 999999) "localhost" -- session-signing cert
  pure . snd $ tlsCredentials (leaf :| [caCreds])

certFingerprint :: X.SignedCertificate -> C.KeyHash
certFingerprint caCert = C.KeyHash fp
  where
    Fingerprint fp = getFingerprint caCert X.HashSHA256

-- | Release only the matching transport and wait for its handler to finish.
-- A delayed disconnect callback can never release a replacement session.
releaseHostSession :: RCHostClient -> SessionCode -> IO ()
releaseHostSession RCHostClient {client_ = RCHClient_ {activeSession}} sid = do
  done <- atomically $ tryReadTMVar activeSession >>= \case
    Just (current, end, finished, tid) | current == sid -> Just (finished, tid) <$ void (tryPutTMVar end ())
    _ -> pure Nothing
  forM_ done $ \(finished, tid) -> killThread tid >> atomically (readTMVar finished)

cancelHostClient :: RCHostClient -> IO ()
cancelHostClient RCHostClient {action, client_ = RCHClient_ {announcer}} = do
  atomically (tryTakeTMVar announcer) >>= mapM_ uninterruptibleCancel
  uninterruptibleCancel action

prepareHostSession :: TVar ChaChaDRG -> C.KeyHash -> RCHostPairing -> RCHostKeys -> RCHostEncHello -> ExceptT RCErrorType IO (RCCtrlEncHello, HostSessKeys, RCHostHello, RCHostPairing)
prepareHostSession
  drg
  tlsHostFingerprint
  pairing@RCHostPairing {idPrivKey, knownHost = knownHost_}
  RCHostKeys {sessKeys = (_, sessPrivKey), dhKeys = (_, dhPrivKey)}
  RCHostEncHello {dhPubKey, nonce, encBody} = do
    let sharedKey = C.dh' dhPubKey dhPrivKey
    helloBody <- liftEitherWith (const RCEDecrypt) $ C.cbDecrypt sharedKey nonce encBody
    hostHello@RCHostHello {v, ca, kem = kemPubKey} <- liftEitherWith RCESyntax $ J.eitherDecodeStrict helloBody
    unless (ca == tlsHostFingerprint) $ throwE RCEIdentity
    (kemCiphertext, kemSharedKey) <- liftIO $ sntrup761Enc drg kemPubKey
    let KEMHybridSecret hybridKey = kemHybridSecret dhPubKey dhPrivKey kemSharedKey
    unless (isCompatible v supportedRCPVRange) $ throwE RCEVersion
    (sndKey, rcvKey) <- bimapM newTVarIO newTVarIO $ C.sbcInit "" hybridKey
    let keys = HostSessKeys {chainKeys = TSbChainKeys {sndKey, rcvKey}, idPrivKey, sessPrivKey}
    knownHost' <- updateKnownHost ca dhPubKey
    let ctrlHello = RCCtrlHello {}
    -- TODO send error response if something fails
    (sk, nonce') <- atomically $ stateTVar sndKey C.sbcHkdf
    encBody' <- liftEitherWith (const RCEBlockSize) $ C.sbEncrypt sk nonce' (LB.toStrict $ J.encode ctrlHello) helloBlockSize
    let ctrlEncHello = RCCtrlEncHello {kem = kemCiphertext, encBody = encBody'}
    pure (ctrlEncHello, keys, hostHello, pairing {knownHost = Just knownHost'})
    where
      updateKnownHost :: C.KeyHash -> C.PublicKeyX25519 -> ExceptT RCErrorType IO KnownHostPairing
      updateKnownHost ca hostDhPubKey = case knownHost_ of
        Just h -> do
          unless (hostFingerprint h == tlsHostFingerprint) . throwE $
            RCEInternal "TLS host CA is different from host pairing, should be caught in TLS handshake"
          pure (h :: KnownHostPairing) {hostDhPubKey}
        Nothing -> pure KnownHostPairing {hostFingerprint = ca, hostDhPubKey}

data RCCtrlClient = RCCtrlClient
  { action :: Async (),
    client_ :: RCCClient_
  }

data RCCClient_ = RCCClient_
  { confirmSession :: TMVar Bool,
    endSession :: TMVar ()
  }

type RCCtrlConnection = (RCCtrlClient, RCStepTMVar (SessionCode, TLS 'TClient, RCStepTMVar (RCCtrlSession, RCCtrlPairing)))

-- Dedicated TLS ALPN on the existing port: no multicast or extra listener.
-- The response is protected by a fresh, mutually authenticated TLS channel.
-- Never accept a response on a connection where ALPN was not negotiated.
invitationALPN :: ByteString
invitationALPN = "simplex-xrcp-invitation/1"

requestRCCtrlInvitation :: TVar ChaChaDRG -> RCCtrlPairing -> TransportHost -> Word16 -> ExceptT RCErrorType IO RCVerifiedInvitation
requestRCCtrlInvitation drg RCCtrlPairing {caKey, caCert, ctrlFingerprint, idPubKey} host port =
  (`catchAllErrors` throwE) $
    timeoutThrow RCENotDiscovered 15000000 $ do
      credentials <- liftIO $ genTLSCredentials drg caKey caCert
      let cfg = defaultTransportClientConfig {clientCredentials = Just credentials, clientALPN = Just [invitationALPN]}
      ExceptT . runTransportClient cfg Nothing host (show port) (Just ctrlFingerprint) $ \tls -> runExceptT $ do
        unless (tlsALPN tls == Just invitationALPN) $ throwE RCEVersion
        Large encoded <- receiveRCPacket tls
        signed <- liftEitherWith RCESyntax $ strDecode encoded
        verified@(RCVerifiedInvitation RCInvitation {ca, idkey}) <- maybe (throwE RCEInvitation) pure $ verifySignedInvitation signed
        unless (ca == ctrlFingerprint && idkey == idPubKey) $ throwE RCEIdentity
        pure verified

-- app should determine whether it is a new or known pairing based on CA fingerprint in the invitation
connectRCCtrl :: TVar ChaChaDRG -> RCVerifiedInvitation -> Maybe RCCtrlPairing -> J.Value -> ExceptT RCErrorType IO RCCtrlConnection
connectRCCtrl drg (RCVerifiedInvitation inv@RCInvitation {ca, idkey}) pairing_ hostAppInfo = do
  pairing' <- maybe (liftIO newCtrlPairing) updateCtrlPairing pairing_
  connectRCCtrl_ drg pairing' inv hostAppInfo
  where
    newCtrlPairing :: IO RCCtrlPairing
    newCtrlPairing = do
      ((_, caKey), caCert) <- genCredentials drg Nothing (1, 24 * 999999) "ca"
      (_, dhPrivKey) <- atomically $ C.generateKeyPair drg
      pure RCCtrlPairing {caKey, caCert, ctrlFingerprint = ca, idPubKey = idkey, dhPrivKey, prevDhPrivKey = Nothing}
    updateCtrlPairing :: RCCtrlPairing -> ExceptT RCErrorType IO RCCtrlPairing
    updateCtrlPairing pairing@RCCtrlPairing {ctrlFingerprint, idPubKey, dhPrivKey = currDhPrivKey} = do
      unless (ca == ctrlFingerprint && idPubKey == idkey) $ throwE RCEIdentity
      (_, dhPrivKey) <- atomically $ C.generateKeyPair drg
      pure pairing {dhPrivKey, prevDhPrivKey = Just currDhPrivKey}

connectRCCtrl_ :: TVar ChaChaDRG -> RCCtrlPairing -> RCInvitation -> J.Value -> ExceptT RCErrorType IO RCCtrlConnection
connectRCCtrl_ drg pairing'@RCCtrlPairing {caKey, caCert} inv@RCInvitation {ca, host, port} hostAppInfo = do
  r <- newEmptyTMVarIO
  c <- liftIO mkClient
  action <- liftIO . async . void . runExceptT $ runClient c r `putRCError` r
  pure (RCCtrlClient {action, client_ = c}, r)
  where
    mkClient :: IO RCCClient_
    mkClient = do
      confirmSession <- newEmptyTMVarIO
      endSession <- newEmptyTMVarIO
      pure RCCClient_ {confirmSession, endSession}
    runClient :: RCCClient_ -> RCStepTMVar (SessionCode, TLS 'TClient, RCStepTMVar (RCCtrlSession, RCCtrlPairing)) -> ExceptT RCErrorType IO ()
    runClient RCCClient_ {confirmSession, endSession} r = do
      clientCredentials <- liftIO $ Just <$> genTLSCredentials drg caKey caCert
      let clientConfig = defaultTransportClientConfig {clientCredentials}
      ExceptT . runTransportClient clientConfig Nothing host (show port) (Just ca) $ \tls@TLS {tlsBuffer, tlsContext} -> runExceptT $ do
        -- pump socket to detect connection problems
        liftIO $ peekBuffered tlsBuffer 100000 (TLS.recvData tlsContext) >>= logDebug . tshow -- should normally be ("", Nothing) here
        logDebug "Got TLS connection"
        r' <- newEmptyTMVarIO
        whenM (atomically $ tryPutTMVar r $ Right (tlsUniq tls, tls, r')) $ do
          logDebug "Waiting for session confirmation"
          whenM (atomically $ readTMVar confirmSession) $ runSession tls r' `putRCError` r'
      where
        runSession tls r' = do
          (sharedKey, kemPrivKey, hostEncHello) <- prepareHostHello drg pairing' inv hostAppInfo
          sendRCPacket tls hostEncHello
          ctrlEncHello <- receiveRCPacket tls
          logDebug "Received ctrl HELLO"
          ctrlSessKeys <- prepareCtrlSession pairing' inv sharedKey kemPrivKey ctrlEncHello
          whenM (atomically $ tryPutTMVar r' $ Right (RCCtrlSession {tls, sessionKeys = ctrlSessKeys}, pairing')) $ do
            logDebug "Session started"
            -- release second putTMVar in confirmCtrlSession
            void . atomically $ takeTMVar confirmSession
            atomically $ takeTMVar endSession
            logDebug "Session ended"

putRCError :: ExceptT RCErrorType IO a -> TMVar (Either RCErrorType b) -> ExceptT RCErrorType IO a
a `putRCError` r = a `catchAllErrors` \e -> atomically (tryPutTMVar r $ Left e) >> throwE e

sendRCPacket :: Encoding a => TLS p -> a -> ExceptT RCErrorType IO ()
sendRCPacket tls pkt = do
  b <- liftEitherWith (const RCEBlockSize) $ C.pad (smpEncode pkt) xrcpBlockSize
  liftIO $ cPut tls b

receiveRCPacket :: Encoding a => TLS p -> ExceptT RCErrorType IO a
receiveRCPacket tls = do
  b <- liftIO $ cGet tls xrcpBlockSize
  when (B.length b /= xrcpBlockSize) $ throwE RCEBlockSize
  b' <- liftEitherWith (const RCEBlockSize) $ C.unPad b
  liftEitherWith RCESyntax $ smpDecode b'

prepareHostHello :: TVar ChaChaDRG -> RCCtrlPairing -> RCInvitation -> J.Value -> ExceptT RCErrorType IO (C.DhSecretX25519, KEMSecretKey, RCHostEncHello)
prepareHostHello
  drg
  RCCtrlPairing {caCert, dhPrivKey}
  RCInvitation {v, dh = dhPubKey}
  hostAppInfo = do
    logDebug "Preparing session"
    case compatibleVersion v supportedRCPVRange of
      Nothing -> throwE RCEVersion
      Just (Compatible v') -> do
        nonce <- liftIO . atomically $ C.randomCbNonce drg
        (kemPubKey, kemPrivKey) <- liftIO $ sntrup761Keypair drg
        let helloBody = RCHostHello {v = v', ca = certFingerprint caCert, app = hostAppInfo, kem = kemPubKey}
            sharedKey = C.dh' dhPubKey dhPrivKey
        encBody <- liftEitherWith (const RCEBlockSize) $ C.cbEncrypt sharedKey nonce (LB.toStrict $ J.encode helloBody) helloBlockSize
        -- let sessKeys = CtrlSessKeys {hybridKey, idPubKey, sessPubKey = skey}
        let hostEncHello = RCHostEncHello {dhPubKey = C.publicKey dhPrivKey, nonce, encBody}
        pure (sharedKey, kemPrivKey, hostEncHello)

prepareCtrlSession :: RCCtrlPairing -> RCInvitation -> C.DhSecretX25519 -> KEMSecretKey -> RCCtrlEncHello -> ExceptT RCErrorType IO CtrlSessKeys
prepareCtrlSession
  RCCtrlPairing {idPubKey, dhPrivKey}
  RCInvitation {skey, dh = dhPubKey}
  sharedKey
  kemPrivKey = \case
    RCCtrlEncHello {kem = kemCiphertext, encBody} -> do
      kemSharedKey <- liftIO $ sntrup761Dec kemCiphertext kemPrivKey
      let KEMHybridSecret hybridKey = kemHybridSecret dhPubKey dhPrivKey kemSharedKey
      -- keys are swapped in controller
      (sndKey, rcvKey) <- swap <$> bimapM newTVarIO newTVarIO (C.sbcInit "" hybridKey)
      (sk, nonce) <- atomically $ stateTVar rcvKey C.sbcHkdf
      helloBody <- liftEitherWith (const RCEDecrypt) $ C.sbDecrypt sk nonce encBody
      logDebug "Decrypted ctrl HELLO"
      RCCtrlHello {} <- liftEitherWith RCESyntax $ J.eitherDecodeStrict helloBody
      pure CtrlSessKeys {chainKeys = TSbChainKeys {sndKey, rcvKey}, idPubKey, sessPubKey = skey}
    RCCtrlEncError {nonce, encMessage} -> do
      message <- liftEitherWith (const RCEDecrypt) $ C.cbDecrypt sharedKey nonce encMessage
      throwE $ RCECtrlError $ T.unpack $ safeDecodeUtf8 message

-- * Multicast discovery

announceRC :: TVar ChaChaDRG -> Int -> C.PrivateKeyEd25519 -> C.PublicKeyX25519 -> RCHostKeys -> RCInvitation -> ExceptT RCErrorType IO ()
announceRC drg maxCount idPrivKey knownDhPub RCHostKeys {sessKeys, dhKeys} inv = ExceptT $ withSender $ \sender -> runExceptT $ do
  replicateM_ maxCount $ do
    logDebug "Announcing..."
    nonce <- atomically $ C.randomCbNonce drg
    encInvitation <- liftEitherWith (const RCEEncrypt) $ C.cbEncrypt sharedKey nonce sigInvitation encInvitationSize
    liftIO . UDP.send sender $ smpEncode RCEncInvitation {dhPubKey, nonce, encInvitation}
    threadDelay 1000000
  where
    sigInvitation = strEncode $ signInvitation sPrivKey idPrivKey inv
    (_sPub, sPrivKey) = sessKeys
    sharedKey = C.dh' knownDhPub dhPrivKey
    (dhPubKey, dhPrivKey) = dhKeys

discoverRCCtrl :: TMVar Int -> NonEmpty RCCtrlPairing -> ExceptT RCErrorType IO (RCCtrlPairing, RCVerifiedInvitation)
discoverRCCtrl subscribers pairings =
  timeoutThrow RCENotDiscovered 30000000 $ ExceptT $ withListener subscribers $ \listener ->
    runExceptT . loop $ do
      (source, bytes) <- liftIO $ recvAnnounce listener
      encInvitation <- liftEitherWith (const RCEInvitation) $ smpDecode bytes
      r@(_, RCVerifiedInvitation RCInvitation {host}) <- findRCCtrlPairing pairings encInvitation
      case source of
        SockAddrInet _ ha | THIPv4 (hostAddressToTuple ha) == host -> pure ()
        _ -> throwE RCEInvitation
      pure r
  where
    loop :: ExceptT RCErrorType IO a -> ExceptT RCErrorType IO a
    loop action = action `catchAllErrors` \e -> logError (tshow e) >> loop action

findRCCtrlPairing :: NonEmpty RCCtrlPairing -> RCEncInvitation -> ExceptT RCErrorType IO (RCCtrlPairing, RCVerifiedInvitation)
findRCCtrlPairing pairings RCEncInvitation {dhPubKey, nonce, encInvitation} = do
  (pairing, signedInvStr) <- liftEither $ decrypt (L.toList pairings)
  signedInv <- liftEitherWith RCESyntax $ strDecode signedInvStr
  inv@(RCVerifiedInvitation RCInvitation {dh = invDh, ts}) <- maybe (throwE RCEInvitation) pure $ verifySignedInvitation signedInv
  unless (invDh == dhPubKey) $ throwE RCEInvitation
  now <- systemSeconds <$> liftIO getSystemTime
  unless (now - 3660 <= systemSeconds ts && systemSeconds ts <= now + 3600) $ throwE RCEInvitation
  pure (pairing, inv)
  where
    decrypt :: [RCCtrlPairing] -> Either RCErrorType (RCCtrlPairing, ByteString)
    decrypt [] = Left RCECtrlNotFound
    decrypt (pairing@RCCtrlPairing {dhPrivKey, prevDhPrivKey} : rest) =
      let r = decrypt_ dhPrivKey <|> (decrypt_ =<< prevDhPrivKey)
       in maybe (decrypt rest) (Right . (pairing,)) r
    decrypt_ :: C.PrivateKeyX25519 -> Maybe ByteString
    decrypt_ dhPrivKey =
      let key = C.dh' dhPubKey dhPrivKey
       in eitherToMaybe $ C.cbDecrypt key nonce encInvitation

-- * Controller handle operations

-- application should call this function when TMVar resolves
confirmCtrlSession :: RCCtrlClient -> Bool -> IO ()
confirmCtrlSession RCCtrlClient {client_ = RCCClient_ {confirmSession}} res = do
  atomically $ putTMVar confirmSession res
  -- controler does takeTMVar, freeing the slot
  -- TODO add timeout
  atomically $ putTMVar confirmSession res -- wait for Ctrl to take the var

cancelCtrlClient :: RCCtrlClient -> IO ()
cancelCtrlClient RCCtrlClient {action, client_ = RCCClient_ {endSession}} = do
  atomically $ void $ tryPutTMVar endSession ()
  uninterruptibleCancel action

-- * Session encryption

rcEncryptBody :: C.SbKeyNonce -> LazyByteString -> ExceptT RCErrorType IO LazyByteString
rcEncryptBody keyNonce s = do
  liftEitherWith (const RCEEncrypt) $ LC.sbEncryptTailTagNoPad keyNonce s

rcDecryptBody :: C.SbKeyNonce -> LazyByteString -> ExceptT RCErrorType IO LazyByteString
rcDecryptBody keyNonce ct = do
  let len = LB.length ct - 16
  when (len < 0) $ throwE RCEDecrypt
  (ok, s) <- liftEitherWith (const RCEDecrypt) $ LC.sbDecryptTailTagNoPad keyNonce len ct
  unless ok $ throwE RCEDecrypt
  pure s
