{-# OPTIONS_GHC -fno-warn-orphans -XPatternGuards #-}
-- |
-- Module      : Scion.Utils
-- Copyright   : (c) Thomas Schilling 2008
-- License     : BSD-style
--
-- Maintainer  : nominolo@gmail.com
-- Stability   : experimental
-- Portability : portable
--
-- Various utilities.
--
module Scion.Utils where

import Scion.Types

import GHC              ( GhcMonad, ModSummary, spans, getLoc, Located
                        , depanal, topSortModuleGraph, TypecheckedMod
                        , mkPrintUnqualifiedForModule, moduleInfo )
import Digraph          ( flattenSCCs )
import Outputable

import Control.Monad
import Data.Maybe ( fromMaybe )

import Data.Char (isLower, isUpper)

import Text.JSON

import Data.Foldable (foldlM)

import System.FilePath

import System.Directory (doesFileExist)

import System.IO (openFile, hPutStrLn, hClose, IOMode(..))

import Data.List (isPrefixOf)

thingsAroundPoint :: (Int, Int) -> [Located n] -> [Located n]
thingsAroundPoint pt ls = [ l | l <- ls, spans (getLoc l) pt ]

modulesInDepOrder :: GhcMonad m => m [ModSummary]
modulesInDepOrder = do
  gr <- depanal [] False
  return $ flattenSCCs $ topSortModuleGraph False gr Nothing
  
-- in dep-order
foldModSummaries :: GhcMonad m =>
                    (a -> ModSummary -> m a) -> a
                 -> m a
foldModSummaries f seed =
  modulesInDepOrder >>= foldM f seed


expectJust :: String -> Maybe a -> a
expectJust _ (Just a) = a
expectJust msg Nothing = 
    dieHard $ "Just x expected.\n  grep for \"" ++ msg ++ "\""

unqualifiedForModule :: TypecheckedMod m => m -> ScionM PrintUnqualified
unqualifiedForModule tcm = do
  fromMaybe alwaysQualify `fmap` mkPrintUnqualifiedForModule (moduleInfo tcm)

second :: (a -> b) -> (c, a) -> (c, b)
second f (x,y) = (x, f y)

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM cm tm em = do
  c <- cm
  if c then tm else em


------------------------------------------------------------------------
-- JSON helper functions


------------------------------------------------------------------------------


-- an alternative to the broken Fuzzy module
-- match sH simpleHTTP
-- match siH simpleHTTP
-- match sHTTP simpleHTTP
-- match pSL putStrLn
-- match lM liftM
-- match DS Data.Set
camelCaseMatch :: String -> String -> Bool
camelCaseMatch (c:cs) (i:is)
  | c == i = (camelCaseMatch cs $ dropWhile (\c' -> isLower c' || c' == '.') . dropWhile isUpper $ is)
          || camelCaseMatch cs is -- to allow siH match simpleHTTP
  | otherwise = False
camelCaseMatch [] [] = True
camelCaseMatch [] _ = False
camelCaseMatch _ [] = False


instance JSON CabalConfiguration where
  readJSON (JSObject obj)
    | Ok "build-configuration" <- lookupKey obj "type"
    , Ok distDir' <- lookupKey obj "dist-dir"
    , Ok args     <- lookupKey obj "extra-args"
    , Ok args2    <- readJSONs args
    = return $ CabalConfiguration distDir' args2
  readJSON _ = fail "CabalConfiguration"
  showJSON (CabalConfiguration dd ea) = makeObject [
        ("dist-dir", JSString (toJSString dd))
      , ("extra-args", JSArray (map (JSString . toJSString) ea)) ]


data ScionDefaultCabalConfig = ScionDefaultCabalConfig String
instance JSON ScionDefaultCabalConfig where
  readJSON (JSObject obj)
    | Ok s <- lookupKey obj "scion-default-cabal-config"
    = return $ ScionDefaultCabalConfig s
  readJSON _ = fail "ScionDefaultCabalConfig"
  showJSON (ScionDefaultCabalConfig s) = makeObject $ [ ("scion-default-cabal-config", (JSString . toJSString) s) ]

readFileComponentConfig :: JSValue -> Result (String, [String])

readFileComponentConfig (JSObject obj)
    | Ok "component-file" <- lookupKey obj "type"
    , Ok file <- lookupKey obj "file"
    , Ok args     <- lookupKey obj "flags"
    , Ok args2    <- readJSONs args
    = return (file, args2)
readFileComponentConfig _ = fail "reading component-file config"

projectConfigFileFromDir :: FilePath -> FilePath
projectConfigFileFromDir = (</> ".scion-config")
projectConfigFromDir :: FilePath -> ScionM ScionProjectConfig
projectConfigFromDir = parseScionProjectConfig . projectConfigFileFromDir

-- If the file exists append. Deleting settings you don't need is faster than looking them up.. 
-- So let's extend this creating a complete reference?
-- Maybe we can even add flags from the cabal file automatically ?
writeSampleConfig :: FilePath -> IO ()
writeSampleConfig file = do
  h <- openFile file AppendMode
  hPutStrLn h $ "\n" ++ unlines [
             "// this is a demo scion project configuration file has been created for you"
            ,"// you can use it to write down a set of configurations you'd like to test"
            ,"//"
            ,"// make scion select the default scion entry"
            ,"{\"scion-default-cabal-config\":\"dist-scion\"}"
            ,"// default scion entry:"
            ,"{\"type\":\"build-configuration\", \"dist-dir\":\"dist-scion\", \"extra-args\": [], \"scion-default\": 1}"
            ,"//"
            ,"// some examples:"
            ,"{\"type\":\"build-configuration\", \"dist-dir\":\"dist-demo-simple-tools-from-path-default\", \"extra-args\": []}"
            ,"{\"type\":\"build-configuration\", \"dist-dir\":\"dist-demo-1\", \"extra-args\": [\"--with-hc-pkg=PATH\", \"--with-compiler=path-to-ghc\"]}"
            ,"{\"type\":\"build-configuration\", \"dist-dir\":\"dist-demo-2\", \"extra-args\": [\"--flags=BuildTestXHTML BuildTestSimple\", \"--disable-library-profiling\"]}"
            ,"//"
            ,"{\"type\":\"component-file\", \"file\": \"test-application.hs\", \"flags\":[\"-package\", \"parsec\"]}"
            ,"{\"type\":\"component-file\", \"file\": \"test-application.hs\", \"flags\":[]}"
          ]
  hClose h

-- TODO ensure file handle is closed!
-- the format of this file will change when scion matures..
-- However it's a quick and easy way for scion, the client and users to read and write the config
parseScionProjectConfig :: FilePath -> ScionM ScionProjectConfig
parseScionProjectConfig path = do
    de <- liftIO $ doesFileExist path
    if de
      then do
        lines' <- liftIO $ liftM ( filter (not . isPrefixOf "//") . lines) $ readFile path
        jsonParsed <- mapM parseLine lines'
        foldlM parseJSON emptyScionProjectConfig jsonParsed
      else return emptyScionProjectConfig
  where
    parseLine :: String -> ScionM JSValue
    parseLine l = case decodeStrict l of
      Ok r -> return r
      Error msg -> scionError $ "error parsing configuration line" ++ (show l) ++ " error : " ++ msg
    parseJSON :: ScionProjectConfig -> JSValue -> ScionM ScionProjectConfig
    parseJSON pc json = case readJSON json of
      Ok bc -> return $ pc { buildConfigurations = bc : buildConfigurations pc }
      Error msg1 -> case readFileComponentConfig json of
        Ok cf -> return $ pc { fileComponentExtraFlags = cf : fileComponentExtraFlags pc }
        Error msg2 -> case readJSON json of
          Ok (ScionDefaultCabalConfig name) -> return $ pc { scionDefaultCabalConfig = Just name }
          Error msg3 -> scionError $ "invalid JSON object " ++ (show json) ++ " error :" ++ msg1 ++ "\n" ++ msg2 ++ "\n" ++ msg3

