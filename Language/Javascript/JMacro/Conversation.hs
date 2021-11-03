{-# LANGUAGE QuasiQuotes, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}

{- |
Module      :  Language.Javascript.JMacro.Conversation
Copyright   :  (c) Gershom Bazerman, 2010
License     :  BSD 3 Clause
Maintainer  :  gershomb@gmail.com
Stability   :  experimental


> testRPCCall :: String -> JExpr -> JExpr -> JExpr
> (testRPC, testRPCCall) = mkWebRPC "test" $ \x y -> asIO $ return (x + (y::Int))

-}

module Language.Javascript.JMacro.Conversation (
   mkWebRPC, asIO, Request, Response(..), WebRPCDesc, WebConvRPC
) where

import Prelude hiding (tail, init, head, last, minimum, foldr1, foldl1, (!!), read)

import Control.Concurrent
import Control.Monad.Trans
import Control.Monad
import Data.Monoid
import Data.Time
import qualified Data.IntMap as IM

import Text.Html
import Text.JSON
import Text.JSON.String

import Language.Javascript.JMacro.Base
import Language.Javascript.JMacro.QQ
import Language.Javascript.JMacro.Rpc

type WebConvRPCDesc = (String, (Int,Request) -> IO Response)

type WebConvRPC a = ((Int -> IO (MVar a)) -> WebConvRPCDesc, ConvRPC)

-- | usage: mkWebConversationPage delays emptyConversation rpcs pagegenerationfunction
-- Delays is a triple which controls how often (in microseconds) a reaper thread runs to delete unused conversations, how often (in milliseconds) the client webpage pings the server to let it know that it's still alive, an how long (in seconds) since the last ping that a page is considered alive before the reaper thread culls its state. A good value would be (300000000,300000,900) -- i.e. (5 minutes, 5 minutes, 15 minutes).
mkConversationPage
  :: (MonadIO m) =>
     (Int,Int,Int)
     -> conv
     -> [WebConvRPC conv]
     -> (JStat -> m b)
     -> IO (m b, [WebConvRPCDesc])
mkConversationPage delays ec rpcs pg = do
  mv <- liftIO $ newMVar IM.empty
  mkConversationPage' delays mv ec rpcs pg

mkConversationPage' (reapDelay,pingbackDelay,maxTimeout) conversations emptyConv rpcs pg = do
  cidCount <- liftIO $ newMVar . (+1) . maximum . (0:) . IM.keys =<< readMVar conversations
  let
      myPg = do
        newCid <- liftIO $ modifyMVar cidCount $ \i -> return (i+1,i)
        t <- liftIO $ getCurrentTime
        liftIO $ modifyMVar_ conversations $
             \cs -> case IM.lookup newCid cs of
                             Just _ -> error $ "Conversation already exists: " ++ show newCid
                             Nothing -> do
                                 x <- newMVar emptyConv
                                 return $ IM.insert newCid (x,t) cs
        pg (myJs newCid)

      myJs cid = jsCallRemote `mappend`
                   [jmacro|
                      jm_conversation_id=`(cid)`;
                      `(defRPCs (map snd rpcs))`;
                      $(\ {
                          fun pingback {
                                setTimeout(pingback, `(pingbackDelay)`);
                                callRemote true (document.URL.match(/[^?^#]*/)[0] + "/rpcs/ping") [];
                          }
                          pingback();
                        });
                    |]

      getConv cid = do
          t <- getCurrentTime
          modifyMVar conversations $
             \cs -> case IM.lookup cid cs of
                             Just (x,_t) -> return (IM.insert cid (x,t) cs ,x)
                             Nothing -> error $ "Conversation has been expired. Please reload."
      (pingRPC,_) = mkWebConvRPC "ping" $ \gc -> gc >> return ()

      myRpcs = map ($ getConv) (pingRPC : map fst rpcs)

      maxTimeout = 15 * 60 -- 15 minutes

      reapConversations = do
               now <- getCurrentTime
               modifyMVar_ conversations $ \c -> do
                            return . IM.fromList . filter ((< maxTimeout) . diffUTCTime now . snd . snd) . IM.toList $ c

  forkIO $ forever $ reapConversations >> threadDelay reapDelay

  return (myPg, myRpcs)


data ConvRPC = ConvRPC String Int deriving Show -- name, arity

class DefConvRPC a where
    defConvRPC_ :: String -> Int -> a -> ConvRPC

instance DefConvRPC (IO b) where
    defConvRPC_ nm arity _ = ConvRPC nm arity

instance DefConvRPC b => DefConvRPC (a -> b) where
    defConvRPC_ nm arity f = defConvRPC_ nm (arity + 1) (f undefined)

defConvRPC :: (DefConvRPC a) => String -> a -> ConvRPC
defConvRPC nm f = defConvRPC_ nm 0 f

--todo arity check
defRPCs :: [ConvRPC] -> JStat
defRPCs cs = mconcat $ map defIt cs
    where defIt (ConvRPC nm arity) = BlockStat [
                 DeclStat (StrI nm) Nothing
               , AssignStat (ValExpr (JVar (StrI nm)))
                   [jmacroE|\ -> callRemote false (document.URL.match(/[^?^#]*/)[0] + "/rpcs/" + `(nm)`) (toList arguments)|]
              ]


mkWebConvRPC  :: (ToWebRPC a1, DefConvRPC a1) => String -> (IO (MVar conv) -> a1) -> WebConvRPC conv
mkWebConvRPC nm rpcFun =
    (\getConv -> (nm, toWebConvRPC getConv rpcFun),
     defConvRPC nm (rpcFun undefined))


toWebConvRPC getConv f = \req -> case runGetJSON readJSArray (snd req) of
                 (Right (JSArray xs)) -> f' (getCid req) xs
                 (Left e) -> return $ BadResponse 400 $ "Bad Data format: " ++  e
                 _ -> return $ BadResponse 400 "Bad Data format: toWebRPC error"
    where f' cid = toWebRPC_ $ f (getConv cid)
          getCid req = fst req



jsCallRemote = [jmacro|
              var !jm_conversation_id = null;
              fun callRemote silentAndAsync loc args {
                   var res = null;
                   $.ajax(
                         {type    : "POST",
                          url     : loc ,
                          data    : { args : JSON.stringify args ,
                                      conversation_id : jm_conversation_id
                                    },
                          success : \d {res = d},
                          error   : \x _s t {
                                      if(silentAndAsync) {
                                        return null;
                                      }
                                      var rt = unquote "\"" "\"" x.responseText;
                                      if (rt.length > 0) {
                                        alert rt;
                                      } else {
                                        alert ("Failed to connect to server: " + t.name);
                                      }
                                    },
                          dataType: "json",
                          async   : silentAndAsync
                         });
                      return res;
                    }|]
