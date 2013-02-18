{-# LANGUAGE ScopedTypeVariables, CPP, PatternGuards, 
             ExistentialQuantification #-} -- for 'Cmd'
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Scion.Server.Commands
-- Copyright   : (c) Thomas Schilling 2008
-- License     : BSD-style
-- 
-- Maintainer  : nominolo@gmail.com
-- Stability   : experimental
-- Portability : portable
-- 
-- Commands provided by the server.
-- 
-- TODO: Need some way to document the wire protocol.  Autogenerate?
-- 
module Scion.Server.Commands ( 
  handleRequest, malformedRequest, -- allCommands, allCommands',
  -- these are reused in the vim interface 
  supportedPragmas, allExposedModules,
) where

import Prelude as P
import Scion.Types
import Scion.Types.Notes
import Scion.Types.Outline
import Scion.Utils
import Scion.Session
import Scion.Server.Protocol
import Scion.Inspect
import Scion.Inspect.DefinitionSite
import Scion.Inspect.PackageDB
import Scion.Cabal
import Scion.Ghc hiding ( (<+>) )

import DynFlags ( supportedLanguages, allFlags )
import Exception
import FastString
import PprTyThing ( pprTypeForUser )
import qualified Outputable as O ( (<+>) )

import Control.Applicative
import Control.Monad
import Data.List ( nub )
import Data.Time.Clock  ( NominalDiffTime )
import System.Exit ( ExitCode(..) )
import Text.JSON
import qualified Data.Map as M
import qualified Data.MultiSet as MS

import GHC.SYB.Utils

#ifndef HAVE_PACKAGE_DB_MODULES
import UniqFM ( eltsUFM )
import Packages ( pkgIdMap )
  
import Distribution.InstalledPackageInfo
#endif

type KeepGoing = Bool

-- a scion request is JS object with 3 keys:
-- method: the method to be called
-- params: arguments to be passed 
-- id    : this value will be passed back to the client
--         to identify a reply to a specific request
--         asynchronous requests will be implemented in the future
handleRequest :: JSValue -> ScionM (JSValue, KeepGoing)
handleRequest (JSObject req) =
  let request = do JSString method <- lookupKey req "method"
                   params <- lookupKey req "params"
                   seq_id <- lookupKey req "id"
                   return (fromJSString method, params, seq_id)
  in 
  case request of
    Error _ -> return (malformedRequest, True)
    Ok (method, params, seq_id) 
     | method == "quit" -> return (makeObject 
                             [("version", str "0.1")
                             ,("result", JSNull)
                             ,("id", seq_id)], False)
     | otherwise ->
      case M.lookup method allCmds of
        Nothing -> return (unknownCommand seq_id, True)
        Just (Cmd _ arg_parser) ->
          decode_params params arg_parser seq_id
 where
   decode_params JSNull arg_parser seq_id =
       decode_params (makeObject []) arg_parser seq_id
   decode_params (JSObject args) arg_parser seq_id =
     case unPa arg_parser args of
       Left err -> return (paramParseError seq_id err, True)
       Right act -> do
           r <- handleScionException act
           case r of
             Error msg -> return (commandExecError seq_id msg, True)
             Ok a ->
                 return (makeObject 
                    [("version", str "0.1")
                    ,("id", seq_id)
                    ,("result", showJSON a)], True)
   decode_params _ _ seq_id =
     return (paramParseError seq_id "Params not an object", True)
  
handleRequest _ = do
  return (malformedRequest, True)
                               
malformedRequest :: JSValue
malformedRequest = makeObject 
 [("version", str "0.1")
 ,("error", makeObject 
    [("name", str "MalformedRequest")
    ,("message", str "Request was not a proper request object.")])]

unknownCommand :: JSValue -> JSValue
unknownCommand seq_id = makeObject 
 [("version", str "0.1")
 ,("id", seq_id)
 ,("error", makeObject 
    [("name", str "UnknownCommand")
    ,("message", str "The requested method is not supported.")])]

paramParseError :: JSValue -> String -> JSValue
paramParseError seq_id msg = makeObject
 [("version", str "0.1")
 ,("id", seq_id)
 ,("error", makeObject 
    [("name", str "ParamParseError")
    ,("message", str msg)])]

commandExecError :: JSValue -> String -> JSValue
commandExecError seq_id msg = makeObject
 [("version", str "0.1")
 ,("id", seq_id)
 ,("error", makeObject 
    [("name", str "CommandFailed")
    ,("message", str msg)])]

allCmds :: M.Map String Cmd
allCmds = M.fromList [ (cmdName c, c) | c <- allCommands ]

------------------------------------------------------------------------

-- | All Commands supported by this Server.
allCommands :: [Cmd]
allCommands = 
    [ cmdConnectionInfo
    , cmdListSupportedLanguages
    , cmdListSupportedPragmas
    , cmdListSupportedFlags
    , cmdListCabalComponents
    , cmdListCabalConfigurations
    , cmdWriteSampleConfig
    , cmdListRdrNamesInScope
    , cmdListExposedModules
    , cmdCurrentComponent
    , cmdSetVerbosity
    , cmdGetVerbosity
    , cmdLoad
    , cmdDumpSources
    , cmdThingAtPoint
    , cmdSetGHCVerbosity
    , cmdBackgroundTypecheckFile
    , cmdBackgroundTypecheckArbitrary
    , cmdAddCmdLineFlag
    , cmdForceUnload
    , cmdDumpDefinedNames
    , cmdDefinedNames
    , cmdNameDefinitions
    , cmdIdentify
    , cmdDumpModuleGraph
    , cmdDumpNameDB
    , cmdToplevelNames
    , cmdOutline
    , cmdTokens
    ]

------------------------------------------------------------------------------

type OkErr a = Result a

-- encode expected errors as proper return values
handleScionException :: ScionM a -> ScionM (OkErr a)
handleScionException m = ((((do
   r <- m
   return (Ok r)
  `gcatch` \(e :: SomeScionException) -> return (Error (show e)))
  `gcatch` \(e' :: GhcException) -> 
               case e' of
                Panic _ -> throw e'
                InstallationError _ -> throw e'
                Interrupted -> throw e'
                _ -> return (Error (show e')))
  `gcatch` \(e :: ExitCode) -> 
                -- client code may not exit the server!
                return (Error (show e)))
  `gcatch` \(e :: IOError) ->
                return (Error (show e)))
--   `gcatch` \(e :: SomeException) ->
--                 liftIO (print e) >> liftIO (throwIO e)

------------------------------------------------------------------------------

newtype Pa a = Pa { unPa :: JSObject JSValue -> Either String a }
instance Monad Pa where
  return x = Pa $ \_ -> Right x
  m >>= k = Pa $ \req -> 
            case unPa m req of
              Left err -> Left err
              Right a -> unPa (k a) req
  fail msg = Pa $ \_ -> Left msg

withReq :: (JSObject JSValue -> Pa a) -> Pa a
withReq f = Pa $ \req -> unPa (f req) req

reqArg' :: JSON a => String -> (a -> b) -> (b -> r) -> Pa r
reqArg' name trans f = withReq $ \req ->
    case lookupKey req name of
      Error _ -> fail $ "required arg missing: " ++ name
      Ok x ->
          case readJSON x of
            Error m -> fail $ "could not decode: " ++ name ++ " - " ++ m
            Ok a -> return (f (trans a))

optArg' :: JSON a => String -> b -> (a -> b) -> (b -> r) -> Pa r
optArg' name dflt trans f = withReq $ \req ->
    case lookupKey req name of
      Error _ -> return (f dflt)
      Ok x -> 
          case readJSON x of
            Error n -> fail $ "could not decode: " ++ name ++ " - " ++ n
            Ok a -> return (f (trans a))

reqArg :: JSON a => String -> (a -> r) -> Pa r
reqArg name f = reqArg' name id f

optArg :: JSON a => String -> a -> (a -> r) -> Pa r
optArg name dflt f = optArg' name dflt id f

noArgs :: r -> Pa r
noArgs = return

infixr 1 <&>

-- | Combine two arguments.
--
-- TODO: explain type
(<&>) :: (a -> Pa b)
      -> (b -> Pa c)
      -> a -> Pa c
a1 <&> a2 = \f -> do f' <- a1 f; a2 f'

data Cmd = forall a. JSON a => Cmd String (Pa (ScionM a))

cmdName :: Cmd -> String
cmdName (Cmd n _) = n

------------------------------------------------------------------------

-- | Used by the client to initialise the connection.
cmdConnectionInfo :: Cmd
cmdConnectionInfo = Cmd "connection-info" $ noArgs worker
  where
    worker = let pid = 0 :: Int in -- TODO for linux: System.Posix.Internals (c_getpid)
             return $ makeObject
               [("version", showJSON scionVersion)
               ,("pid",     showJSON pid)]

decodeBool :: JSValue -> Bool
decodeBool (JSBool b) = b
decodeBool _ = error "no bool"

decodeExtraArgs :: JSValue -> [String]
decodeExtraArgs JSNull = []
decodeExtraArgs (JSString s) =
    words (fromJSString s) -- TODO: check shell-escaping
decodeExtraArgs (JSArray arr) =
    [ fromJSString s | JSString s <- arr ]

instance JSON Component where
  readJSON obj = do
    case readJSON obj of
      Ok (c :: CabalComponent) -> return $ Component c
      _ -> case readJSON obj of
             Ok (c :: FileComp) -> return $ Component c
             _ -> fail $ "Unknown component" ++ show obj

  showJSON (Component c) = showJSON c

instance JSON CompilationResult where
  showJSON (CompilationResult suc notes time) =
      makeObject [("succeeded", JSBool suc)
                 ,("notes", showJSON notes)
                 ,("duration", showJSON time)]
  readJSON (JSObject obj) = do
      JSBool suc <- lookupKey obj "succeeded"
      notes <- readJSON =<< lookupKey obj "notes"
      dur <- readJSON =<< lookupKey obj "duration"
      return (CompilationResult suc notes dur)
  readJSON _ = fail "compilation-result"

instance (Ord a, JSON a) => JSON (MS.MultiSet a) where
  showJSON ms = showJSON (MS.toList ms)
  readJSON o = MS.fromList <$> readJSON o

instance JSON Note where
  showJSON (Note note_kind loc msg) =
    makeObject [("kind", showJSON note_kind)
               ,("location", showJSON loc)
               ,("message", JSString (toJSString msg))]
  readJSON (JSObject obj) = do
    note_kind <- readJSON =<< lookupKey obj "kind"
    loc <- readJSON =<< lookupKey obj "location"
    JSString s <- lookupKey obj "message"
    return (Note note_kind loc (fromJSString s))
  readJSON _ = fail "note"

str :: String -> JSValue
str = JSString . toJSString

instance JSON NoteKind where
  showJSON ErrorNote   = JSString (toJSString "error")
  showJSON WarningNote = JSString (toJSString "warning")
  showJSON InfoNote    = JSString (toJSString "info")
  showJSON OtherNote   = JSString (toJSString "other")
  readJSON (JSString s) =
      case lookup (fromJSString s) 
               [("error", ErrorNote), ("warning", WarningNote)
               ,("info", InfoNote), ("other", OtherNote)]
      of Just x -> return x
         Nothing -> fail "note-kind"
  readJSON _ = fail "note-kind"

instance JSON Location where
  showJSON loc | not (isValidLoc loc) =
    makeObject [("no-location", str (noLocText loc))]
  showJSON loc | (src, l0, c0, l1, c1) <- viewLoc loc =
    makeObject [case src of
                  FileSrc f -> ("file", str (toFilePath f))
                  OtherSrc s -> ("other", str s)
               ,("region", JSArray (map showJSON [l0,c0,l1,c1]))]
  readJSON (JSObject obj) = do
    src <- (do JSString f <- lookupKey obj "file"
               return (FileSrc (mkAbsFilePath "/" (fromJSString f))))
           <|>
           (do JSString s <- lookupKey obj "other"
               return (OtherSrc (fromJSString s)))
    JSArray ls <- lookupKey obj "region"
    case mapM readJSON ls of
      Ok [l0,c0,l1,c1] -> return (mkLocation src l0 c0 l1 c1)
      _ -> fail "region"
  readJSON _ = fail "location"
                      
instance JSON NominalDiffTime where
  showJSON t = JSRational True (fromRational (toRational t))
  readJSON (JSRational _ n) = return $ fromRational (toRational n)
  readJSON _ = fail "diff-time"

instance JSON OutlineDef where
  showJSON t =
    makeObject $ 
      [("name", str $ case od_name t of
  	                Left n -> showSDocUnqual $ ppr n
  	                Right s -> s)
      ,("location", showJSON $ od_loc t)
      ,("block", showJSON $ od_block t)
      ,("type", str $ od_type t)]
      ++
      (case od_parentName t of
  	 Just (n,typ) -> 
             [("parent", makeObject [("name", str $ showSDocUnqual $ ppr $ n)
                                    ,("type", str typ)])]
  	 Nothing -> [])
  readJSON _ = fail "OutlineDef"

instance JSON TokenDef where
  showJSON t | (src, l0, c0, l1, c1) <- viewLoc $ td_loc t =
    makeObject $ 
      [("name", str $ td_name t)
      ,("region", JSArray (map showJSON [l0,c0,l1,c1]))]
  readJSON _ = fail "TokenDef"

cmdListSupportedLanguages :: Cmd
cmdListSupportedLanguages = Cmd "list-supported-languages" $ noArgs cmd
  where cmd = return (map toJSString supportedLanguages)

cmdListSupportedPragmas :: Cmd
cmdListSupportedPragmas = 
    Cmd "list-supported-pragmas" $ noArgs $ return supportedPragmas

supportedPragmas :: [String]
supportedPragmas =
    [ "OPTIONS_GHC", "LANGUAGE", "INCLUDE", "WARNING", "DEPRECATED"
    , "INLINE", "NOINLINE", "RULES", "SPECIALIZE", "UNPACK", "SOURCE"
    , "SCC"
    , "LINE" -- XXX: only used by code generators, still include?
    ]

cmdListSupportedFlags :: Cmd
cmdListSupportedFlags =
  Cmd "list-supported-flags" $ noArgs $ return (nub allFlags)

cmdListRdrNamesInScope :: Cmd
cmdListRdrNamesInScope =
    Cmd "list-rdr-names-in-scope" $ noArgs $ cmd
  where cmd = do
          rdr_names <- getNamesInScope
          return (map (showSDoc . ppr) rdr_names)

cmdListCabalComponents :: Cmd
cmdListCabalComponents =
    Cmd "list-cabal-components" $ reqArg' "cabal-file" fromJSString $ cmd
  where cmd cabal_file = cabalProjectComponents cabal_file

-- return all cabal configurations.
-- currently this just globs for * /setup-config
-- in the future you may write a config file describing the most common configuration settings
cmdListCabalConfigurations :: Cmd
cmdListCabalConfigurations =
    Cmd "list-cabal-configurations" $
      reqArg' "cabal-file" fromJSString <&>
      optArg' "type" "uniq" id <&>
      optArg' "scion-default" False decodeBool $ cmd
  where cmd cabal_file type' scionDefault = liftM showJSON $ cabalConfigurations cabal_file type' scionDefault

cmdWriteSampleConfig :: Cmd
cmdWriteSampleConfig =
    Cmd "write-sample-config" $
      reqArg "file" $ cmd
  where cmd fp = liftIO $ writeSampleConfig fp

allExposedModules :: ScionM [ModuleName]
#ifdef HAVE_PACKAGE_DB_MODULES
allExposedModules = map moduleName `fmap` packageDbModules True
#else
-- This implementation requires our Cabal to be the same as GHC's.
allExposedModules = do
   dflags <- getSessionDynFlags
   let pkg_db = pkgIdMap (pkgState dflags)
   return $ P.concat (map exposedModules (filter exposed (eltsUFM pkg_db)))
#endif

cmdListExposedModules :: Cmd
cmdListExposedModules = Cmd "list-exposed-modules" $ noArgs $ cmd
  where cmd = do
          mod_names <- allExposedModules
          return $ map (showSDoc . ppr) mod_names

cmdSetGHCVerbosity :: Cmd
cmdSetGHCVerbosity =
    Cmd "set-ghc-verbosity" $ reqArg "level" $ setGHCVerbosity

cmdBackgroundTypecheckFile :: Cmd
cmdBackgroundTypecheckFile = 
    Cmd "background-typecheck-file" $ reqArg' "file" fromJSString $ cmd
  where cmd fname = backgroundTypecheckFile fname

cmdBackgroundTypecheckArbitrary :: Cmd
cmdBackgroundTypecheckArbitrary = 
    Cmd "background-typecheck-arbitrary" $ 
        reqArg' "file" fromJSString <&> 
        reqArg' "contents" fromJSString $ cmd
  where cmd fname contents = backgroundTypecheckArbitrary fname contents

cmdForceUnload :: Cmd
cmdForceUnload = Cmd "force-unload" $ noArgs $ unload

cmdAddCmdLineFlag :: Cmd
cmdAddCmdLineFlag = 
    Cmd "add-command-line-flag" $
      optArg' "flag" "" fromJSString <&>
      optArg' "flags" [] (map fromJSString) $ cmd
  where cmd flag flags' = do
          addCmdLineFlags $ (if flag == "" then [] else [flag]) ++ flags'
          return JSNull

cmdThingAtPoint :: Cmd
cmdThingAtPoint =
    Cmd "thing-at-point" $
      reqArg "file" <&> reqArg "line" <&> reqArg "column" $ cmd
  where
    cmd fname line col = do
      let loc = srcLocSpan $ mkSrcLoc (fsLit fname) line col
      tc_res <- gets bgTcCache
      -- TODO: don't return something of type @Maybe X@.  The default
      -- serialisation sucks.
      case tc_res of
        Just (Typechecked tcm) -> do
            --let Just (src, _, _, _, _) = renamedSource tcm
            let src = typecheckedSource tcm
            --let in_range = const True
            let in_range = overlaps loc
            let r = findHsThing in_range src
            --return (Just (showSDoc (ppr $ S.toList r)))
            unqual <- unqualifiedForModule tcm
            case pathToDeepest r of
              Nothing -> return (Just "no info")
              Just (x,xs) ->
                --return $ Just (showSDoc (ppr x O.$$ ppr xs))
                case typeOf (x,xs) of
                  Just t ->
                      return $ Just $ showSDocForUser unqual
                        (prettyResult x O.<+> dcolon O.<+> 
                          pprTypeForUser True t)
                  _ -> return (Just "No info") --(Just (showSDocDebug (ppr x O.$$ ppr xs )))
        _ -> return Nothing

cmdToplevelNames :: Cmd
cmdToplevelNames=
     Cmd "top-level-names" $ noArgs $ cmd
  where
    cmd =do
    tc_res <- gets bgTcCache
    case tc_res of
      Just (Typechecked tcm) -> do
          return $ map (showSDocDump . ppr) $ toplevelNames tcm
      _ -> return []

cmdOutline :: Cmd
cmdOutline =
    Cmd "outline" $  optArg' "trimFile" True decodeBool $ cmd
 where
  cmd trim = do
    root_dir <- projectRootDir
    tc_res <- gets bgTcCache
    case tc_res of
      Just (Typechecked tcm) -> do
        let f = if trim then trimLocationFile else id
        return $ f $ outline root_dir tcm 
      _ -> return []

cmdTokens :: Cmd
cmdTokens = 
     Cmd "tokens" $ reqArg' "file" fromJSString $ cmd
  where cmd fname = do
          root_dir <- projectRootDir
          mb_modsum <- filePathToProjectModule fname
          case mb_modsum of
            Nothing -> do
              return $ Left "Could not find file in module graph."
            Just modsum -> do
                ts<-tokens root_dir $ ms_mod modsum
                return $ Right ts

cmdDumpSources :: Cmd
cmdDumpSources = Cmd "dump-sources" $ noArgs $ cmd
  where 
    cmd = do
      tc_res <- gets bgTcCache
      case tc_res of
        Just (Typechecked tcm)
         | Just rn <- renamedSourceGroup `fmap` renamedSource tcm ->
          do let tc = typecheckedSource tcm
             liftIO $ putStrLn $ showSDocDump $ ppr rn
             liftIO $ putStrLn $ showData TypeChecker 2 tc
             return ()
        _ -> return ()

cmdLoad :: Cmd
cmdLoad = Cmd "load" $ reqArg "component" <&>
    optArg' "output" False decodeBool $ cmd
  where
    cmd comp output= do
      loadComponent' comp output

cmdSetVerbosity :: Cmd
cmdSetVerbosity = 
    Cmd "set-verbosity" $ reqArg "level" $ cmd
  where cmd v = setVerbosity (intToVerbosity v)

cmdGetVerbosity :: Cmd
cmdGetVerbosity = Cmd "get-verbosity" $ noArgs $ verbosityToInt <$> getVerbosity

-- rename to GetCurrentComponent? 
cmdCurrentComponent :: Cmd
cmdCurrentComponent = Cmd "current-component" $ noArgs $ getActiveComponent

cmdDumpDefinedNames :: Cmd
cmdDumpDefinedNames = Cmd "dump-defined-names" $ noArgs $ cmd
  where
    cmd = do db <- gets defSiteDB
             liftIO $ putStrLn $ dumpDefSiteDB db

cmdDefinedNames :: Cmd
cmdDefinedNames = Cmd "defined-names" $ noArgs $ cmd
  where cmd = definedNames <$> gets defSiteDB

cmdNameDefinitions :: Cmd
cmdNameDefinitions =
    Cmd "name-definitions" $ reqArg' "name" fromJSString $ cmd
  where cmd nm = do
          db <- gets defSiteDB
          let locs = map fst $ lookupDefSite db nm
          return locs

cmdIdentify :: Cmd
cmdIdentify =
    Cmd "client-identify" $ reqArg' "name" fromJSString $ cmd
  where cmd c = modifySessionState $ \s -> s { client = c }

cmdDumpModuleGraph :: Cmd
cmdDumpModuleGraph =
   Cmd "dump-module-graph" $ noArgs $ cmd
  where
    cmd = do
      mg <- getModuleGraph
      liftIO $ printDump (ppr mg)
      return ()

cmdDumpNameDB :: Cmd
cmdDumpNameDB =
  Cmd "dump-name-db" $ noArgs $ cmd
 where
   cmd = do
     db <- buildNameDB
     dumpNameDB db
     return ()
