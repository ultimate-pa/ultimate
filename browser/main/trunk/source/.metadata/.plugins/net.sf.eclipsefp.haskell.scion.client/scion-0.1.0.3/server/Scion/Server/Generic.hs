module Scion.Server.Generic 
  ( handle
  ) where

import Prelude hiding ( log )

import Scion
import Scion.Types (gets, SessionState(..))
import Scion.Server.ConnectionIO as CIO
import Scion.Server.Commands

import Text.JSON
import Text.JSON.Types
import qualified Data.ByteString.Lazy.Char8 as S
import qualified Data.ByteString.Lazy.UTF8 as S
import qualified System.Log.Logger as HL

log :: HL.Priority -> String -> IO ()
log = HL.logM "protocol.generic"
logDebug :: MonadIO m => String -> m ()
logDebug = liftIO . log HL.DEBUG

type StopServer = Bool

handle :: (ConnectionIO con) =>
          con
       -> Int
       -> ScionM StopServer
handle con 0 = do
   loop
  where
   loop = do
     -- TODO: don't require line-based input
     str <- liftIO $ CIO.getLine con
     logDebug $ "==> " ++ S.toString str
     let mb_req = decodeStrict (S.toString str)
     (resp, keep_going) 
         <- case mb_req of
              Error _ -> return (malformedRequest, True)
              Ok req -> do
                --logDebug $ "Cmd: " ++ show req
                handleRequest req
     c <- gets client
     let resp_str = encodeStrict (if (c == "vim") then vimHack resp else resp)
     logDebug $ "<== " ++ resp_str
     liftIO $ CIO.putLine con (S.fromString resp_str)
     --logDebug $ "sent response"
     if keep_going then loop else do 
       --logDebug "finished serving connection."
       return True

handle con unknownVersion = do
  -- handshake failure, don't accept this client version 
  liftIO $ CIO.putLine con $ 
    S.pack $ "failure: Don't know how to talk to client version "
      ++ (show unknownVersion)
  return False

-- vim doesn't know about true,false,null thus can't parse it. this functions
-- mapps those values to 1,0,""
vimHack :: JSValue -> JSValue
vimHack JSNull = JSString (toJSString "")
vimHack (JSBool True) = JSRational False 1
vimHack (JSBool False) = JSRational False 0
vimHack (JSArray l) = JSArray $ map vimHack l
vimHack (JSObject (JSONObject list)) = JSObject $ JSONObject $ map (\(x,y) -> (x, vimHack y)) list
vimHack e = e  -- JSRational, JSString 
