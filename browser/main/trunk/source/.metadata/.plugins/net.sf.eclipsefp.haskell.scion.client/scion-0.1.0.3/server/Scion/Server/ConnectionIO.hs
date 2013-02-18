{-# LANGUAGE FlexibleInstances, ExistentialQuantification, MultiParamTypeClasses #-}
-- |
-- Module      : Scion.Server.ConnectionIO
-- License     : BSD-style
--
-- Maintainer  : marco-oweber@gmx.de
-- Stability   : experimental
-- Portability : portable
--
-- Abstraction over Socket and Handle IO.

module Scion.Server.ConnectionIO (
  ConnectionIO(..), mkSocketConnection
) where

import Prelude hiding (log)
import System.IO (Handle, hFlush)
import Network.Socket (Socket)
import Network.Socket.ByteString (recv, send)
import Data.IORef
import qualified System.Log.Logger as HL
import qualified Data.ByteString.Char8 as S
import qualified Data.ByteString.Lazy.Char8 as L

log :: HL.Priority -> String -> IO ()
log = HL.logM "io.connection"

logError :: String -> IO ()
logError = log HL.ERROR

class ConnectionIO con where
  getLine :: con -> IO L.ByteString
  getN    :: con -> Int -> IO L.ByteString
  put     :: con -> L.ByteString -> IO ()
  putLine :: con -> L.ByteString -> IO ()
  putLine c s = put c s >> put c (L.singleton '\n')

-- (stdin,stdout) implemenation 
instance ConnectionIO (Handle, Handle) where
  getLine (i, _) = do l <- S.hGetLine i; return (L.fromChunks [l])
  getN (i,_) = L.hGet i
  put (_,o) = L.hPut o
  putLine (_,o) = \l -> do
      -- ghc doesn't use the ghc api to print texts all the time. So mark
      -- scion replies by a leading "scion:" see README.markdown
      S.hPutStr o scionPrefix
      L.hPut o l
      S.hPutStr o newline
      hFlush o -- don't ask me why this is needed. LineBuffering is set as well (!) 

scionPrefix :: S.ByteString
scionPrefix = S.pack "scion:"

newline :: S.ByteString
newline = S.pack "\n"

data SocketConnection = SockConn Socket (IORef S.ByteString)

mkSocketConnection :: Socket -> IO SocketConnection
mkSocketConnection sock = 
    do r <- newIORef S.empty; return $ SockConn sock r

-- Socket.ByteString implemenation 
instance ConnectionIO SocketConnection where
  -- TODO: Handle client side closing of connection.
  getLine (SockConn sock r) = do 
      buf <- readIORef r
      (line_chunks, buf') <- go buf
      writeIORef r buf'
      return (L.fromChunks line_chunks)
    where
      go buf | S.null buf = do
        chunk <- recv sock 1024
        if S.null chunk
         then return ([], S.empty)
         else go chunk
      go buf =
          let (before, rest) = S.breakSubstring newline buf in
          case () of
           _ | S.null rest -> do
               -- no newline found
               (cs', buf') <- go rest
               return (before:cs', buf')
           _ | otherwise ->
               return ([before], S.drop (S.length newline) rest)

  getN (SockConn sock r) len = do
      buf <- readIORef r
      if S.length buf > len
       then do let (str, buf') = S.splitAt len buf
               writeIORef r buf'
               return (L.fromChunks [str])
       else do
         str <- recv sock (len - S.length buf)
         writeIORef r S.empty
         return (L.fromChunks [buf, str])

  put (SockConn sock _) lstr = do
      go (L.toChunks lstr)
      -- is there a better excption which should be thrown instead?  (TODO)
      -- throw $ mkIOError ResourceBusy ("put in " ++ __FILE__) Nothing Nothing
   where go [] = return ()
         go (str:strs) = do
           let l = S.length str
           sent <- send sock str
           if (sent /= l) then do
             logError $ (show l) ++ " bytes to be sent but could only sent : " ++ (show sent)
            else go strs
