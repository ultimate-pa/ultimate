{-# LANGUAGE ScopedTypeVariables, CPP #-}
{-# LANGUAGE PatternGuards, DeriveDataTypeable #-}
-- |
-- Module      : Scion.Session
-- Copyright   : (c) Thomas Schilling 2008
-- License     : BSD-style
--
-- Maintainer  : nominolo@gmail.com
-- Stability   : experimental
-- Portability : portable
--
-- Utilities to manipulate the session state.
--
module Scion.Session where
-- Imports
import Prelude hiding ( mod )
import GHC hiding ( flags, load )
import DriverPhases (Phase(..),HscSource(..))
import HscTypes ( srcErrorMessages, SourceError, isBootSummary )
import Exception
import StringBuffer (stringToStringBuffer)

import Scion.Types
import Scion.Types.Notes
import Scion.Utils
import Scion.Inspect.DefinitionSite

import qualified Data.MultiSet as MS
import Control.Monad
import Data.Data
import Data.IORef
import Data.Maybe       ( isJust )
import Data.Monoid
import Data.Time.Clock  ( getCurrentTime, diffUTCTime )
import System.Directory ( getCurrentDirectory, canonicalizePath )
import System.FilePath  ( isRelative, makeRelative, normalise, takeExtension )
import System.Time      ( getClockTime )

import Control.Exception
------------------------------------------------------------------------------

-- TODO: have some kind of project description file, that allows us to
-- reconfigure a project when needed.

------------------------------------------------------------------------------

data ComponentDoesNotExist = ComponentDoesNotExist String
     deriving (Show, Typeable)
instance Exception ComponentDoesNotExist where
  toException  = scionToException
  fromException = scionFromException


-- * Setting Session Parameters


initialScionDynFlags :: DynFlags -> DynFlags
initialScionDynFlags dflags =
  dflags {
      -- GHC 6.10.1 has a bug in that it doesn't properly keep track of which
      -- modules were compiled in HscNothing mode.  To avoid this, we use
      -- HscInterpreted.  Unfortunately, that means we cannot use Scion with
      -- projects that use unboxed tuples, as those are not supported by the
      -- byte code compiler.
#ifdef RECOMPILE_BUG_FIXED
      hscTarget = HscNothing  -- by default, don't modify anything
    , ghcLink   = NoLink      -- just to be sure
#else
      hscTarget = HscInterpreted
    , ghcLink   = LinkInMemory
#endif
    }
----------------------------------------------------------------------

-- | Reset the state of the session to a defined default state.
-- 
-- Due to some bugs in GHC this isn't completely possible.  For
-- example, GHC retains instance declarations which can lead to
-- problems when you load a new module which defines a different
-- instance.  (You'll get a conflicting instance error, which can only
-- be resolved by re-starting GHC.)
resetSessionState :: ScionM ()
resetSessionState = do
   unload

   dflags0 <- gets initialDynFlags
   -- TODO: do something with result from setSessionDynFlags?
   setSessionDynFlags (initialScionDynFlags dflags0)
   return ()

-- | Root directory of the current Cabal project.
--
-- Throws:
--
--  * 'NoCurrentCabalProject' if there is no current Cabal project.
--
projectRootDir :: ScionM FilePath
projectRootDir = do
   -- _ <- getLocalBuildInfo -- ensure we have a current project
   -- TODO: error handling
   liftIO (canonicalizePath =<< getCurrentDirectory)

-- | Set GHC's dynamic flags for the given component of the current Cabal
-- project (see 'openCabalProject').
--
-- Throws:
--
--  * 'NoCurrentCabalProject' if there is no current Cabal project.
--
--  * 'ComponentDoesNotExist' if the current Cabal project does not contain
--    the specified component.
--
setComponentDynFlags :: 
       Component 
    -> ScionM [PackageId]
       -- ^ List of packages that need to be loaded.  This corresponds to the
       -- build-depends of the loaded component.
       --
       -- TODO: do something with this depending on Scion mode?
setComponentDynFlags (Component c) = do
  addCmdLineFlags =<< componentOptions c

-- | Set the targets for a 'GHC.load' command from the meta data of
-- the current component.
-- 
-- Throws:
-- 
--  * 'NoCurrentCabalProject' if there is no current Cabal project.
-- 
--  * 'ComponentDoesNotExist' if the current Cabal project does not
--    contain the specified component.
-- 
setComponentTargets :: Component -> ScionM ()
setComponentTargets (Component c) = do
  setTargets =<< componentTargets c

-- | Load the specified component.
-- 
-- Throws:
-- 
--  * 'NoCurrentCabalProject' if there is no current Cabal project.
-- 
--  * 'ComponentDoesNotExist' if the current Cabal project does not
--    contain the specified component.
-- 
loadComponent :: Component
	      -> ScionM CompilationResult
loadComponent comp = loadComponent' comp False

loadComponent' :: Component
	       -> Bool -- ^ Should we build on disk?
               -> ScionM CompilationResult
                  -- ^ The compilation result.
loadComponent' comp output = do
   -- TODO: group warnings by file
   resetSessionState
   setActiveComponent comp
   -- Need to set DynFlags first, so that the search paths are set up
   -- correctly before looking for the targets.
   setComponentDynFlags comp
   dflags0 <- getSessionDynFlags
   let dflags
         | output = dflags0{ hscTarget = defaultObjectTarget
                          , ghcMode = CompManager
                          , ghcLink = LinkBinary
                          }
         | otherwise = dflags0
   setSessionDynFlags dflags
   setComponentTargets comp
   rslt <- load LoadAllTargets
   setSessionDynFlags dflags0    -- Remove LinkBinary
   getDefSiteDB rslt
   return rslt
   
-- | Utility method to regenerate defSiteDB after loading.
getDefSiteDB :: CompilationResult -- ^ The result of loading.
             -> ScionM ()
getDefSiteDB rslt = do
   mg <- getModuleGraph
   base_dir <- projectRootDir
   db <- moduleGraphDefSiteDB base_dir mg
   liftIO $ evaluate db
   modifySessionState $ \s -> s { lastCompResult = rslt
                                , defSiteDB = db }
   return ()

-- | Make the specified component the active one.  Sets the DynFlags
--  to those specified for the given component.  Unloads the possible
-- 
-- Throws:
-- 
--  * 'NoCurrentCabalProject' if there is no current Cabal project.
-- 
--  * 'ComponentDoesNotExist' if the current Cabal project does not
--    contain the specified component.
-- 
setActiveComponent :: Component -> ScionM ()
setActiveComponent the_comp@(Component comp) = do
   curr_comp <- gets activeComponent
   when (needs_unloading curr_comp)
     unload
   r <- componentInit comp
   case r of
     Nothing -> do 
       --setComponentDynFlags the_comp
       modifySessionState $ \sess -> 
           sess { activeComponent = Just the_comp }
     Just msg -> do
       io $ throwIO $ userError msg -- XXX
  where
   needs_unloading (Just c) | c /= the_comp = True
   needs_unloading _ = False

-- | Return the currently active component.
getActiveComponent :: ScionM (Maybe Component)
getActiveComponent = gets activeComponent

------------------------------------------------------------------------
-- * Compilation

-- | Wrapper for 'GHC.load'.
load :: LoadHowMuch -> ScionM CompilationResult
load how_much = do
   start_time <- liftIO $ getCurrentTime
   ref <- liftIO $ newIORef (mempty, mempty)
   res <- loadWithLogger (logWarnErr ref) how_much
            `gcatch` (\(e :: SourceError) -> handle_error ref e)
   end_time <- liftIO $ getCurrentTime
   let time_diff = diffUTCTime end_time start_time
   (warns, errs) <- liftIO $ readIORef ref
   base_dir <- projectRootDir
   let notes = ghcMessagesToNotes base_dir (warns, errs)
   let comp_rslt = case res of
                     Succeeded -> CompilationResult True notes time_diff
                     Failed -> CompilationResult False notes time_diff
   -- TODO: We need to somehow find out which modules were recompiled so we
   -- only update the part that we have new information for.
   modifySessionState $ \s -> s { lastCompResult = comp_rslt }
   return comp_rslt
  where
    logWarnErr ref err = do
      let errs = case err of
                   Nothing -> mempty
                   Just exc -> srcErrorMessages exc
      warns <- getWarnings
      clearWarnings
      add_warn_err ref warns errs

    add_warn_err ref warns errs =
      liftIO $ modifyIORef ref $
                 \(warns', errs') -> ( warns `mappend` warns'
                                     , errs `mappend` errs')

    handle_error ref e = do
       let errs = srcErrorMessages e
       warns <- getWarnings
       add_warn_err ref warns errs
       clearWarnings
       return Failed

-- | Unload whatever is currently loaded.
unload :: ScionM ()
unload = do
   setTargets []
   load LoadAllTargets
   modifySessionState $ \st -> st { lastCompResult = mempty
                                  , defSiteDB = mempty }
   return ()

-- | Parses the list of 'Strings' as command line arguments and sets the
-- 'DynFlags' accordingly.
--
-- Does not set the flags if a parse error occurs.  XXX: There's currently
-- no way to find out if there was an error from inside the program.
addCmdLineFlags :: [String] -> ScionM [PackageId]
addCmdLineFlags flags = do
  message deafening $ "Setting Flags: " ++ show flags
  liftIO $ putStrLn $ "Setting Flags: " ++ show flags
  dflags <- getSessionDynFlags
  res <- gtry $ parseDynamicFlags dflags (map noLoc flags)
  case res of
    Left (UsageError msg) -> do
      liftIO $ putStrLn $ "Dynflags parse error: " ++ msg
      return []
    Left e -> liftIO $ throwIO e
    Right (dflags', unknown, warnings) -> do
      unless (null unknown) $
        liftIO $ putStrLn $ "Unrecognised flags:\n" ++ show (map unLoc unknown)
      liftIO $ mapM_ putStrLn $ map unLoc warnings
      setSessionDynFlags dflags'


-- | Set the verbosity of the GHC API.
setGHCVerbosity :: Int -> ScionM ()
setGHCVerbosity lvl = do
   dflags <- getSessionDynFlags
   setSessionDynFlags $! dflags { verbosity = lvl }
   return ()

------------------------------------------------------------------------------
-- * Background Typechecking

-- | Takes an absolute path to a file and attempts to typecheck it.
--
-- This performs the following steps:
--
--   1. Check whether the file is actually part of the current project.  It's
--      also currently not possible to typecheck a .hs-boot file using this
--      function.  We simply bail out if these conditions are not met.
--
--   2. Make sure that all dependencies of the module are up to date.
--
--   3. Parse, typecheck, desugar and load the module.  The last step is
--      necessary so that we can we don't have to recompile in the case that
--      we switch to another module.
--
--   4. If the previous step was successful, cache the results in the session
--      for use by source code inspection utilities.  Some of the above steps
--      are skipped if we know that they are not necessary.
--
backgroundTypecheckFile :: 
       FilePath 
    -> ScionM (Either String CompilationResult)
       -- ^ First element is @False@ <=> step 1 above failed.
backgroundTypecheckFile fname0 = do
   fname <- liftIO (canonicalizePath fname0)
   root_dir <- projectRootDir
   ifM (not `fmap` isRelativeToProjectRoot fname)
     (return (Left ("file " ++ fname ++ " is not relative to project root " ++ root_dir)))
     (prepareContext fname)
  where
   prepareContext :: FilePath -> ScionM (Either String CompilationResult)
   prepareContext fname = do
     message verbose $ "Preparing context for " ++ fname
     -- if it's the focused module, we know that the context is right
     mb_focusmod <- gets focusedModule
     case mb_focusmod of
       Just ms | Just f <- ml_hs_file (ms_location ms), f == fname -> 
          backgroundTypecheckFile' mempty fname

       _otherwise -> do
          mb_modsum <- filePathToProjectModule fname
          case mb_modsum of
            Nothing -> do
              return $ Left "Could not find file in module graph."
            Just modsum -> do
              (_, rslt) <- setContextForBGTC modsum
              if compilationSucceeded rslt
               then backgroundTypecheckFile' rslt fname
               else return $ Right rslt

   backgroundTypecheckFile' comp_rslt fname = do
      message verbose $ "Background type checking: " ++ fname
      clearWarnings
      start_time <- liftIO $ getCurrentTime
      modsum <- preprocessModule fname

      let finish_up tc_res errs = do
              base_dir <- projectRootDir
              warns <- getWarnings
              clearWarnings
              let notes = ghcMessagesToNotes base_dir (warns, errs)
              end_time <- liftIO $ getCurrentTime
              let ok = isJust tc_res
              let res = CompilationResult ok notes
                                          (diffUTCTime end_time start_time)
              let abs_fname = mkAbsFilePath base_dir fname
              full_comp_rslt <- removeMessagesForFile abs_fname =<< gets lastCompResult
              let comp_rslt' =  full_comp_rslt `mappend` comp_rslt `mappend` res

              modifySessionState (\s -> s { bgTcCache = tc_res
                                          , lastCompResult = comp_rslt' })

              return $ Right comp_rslt'

      ghandle (\(e :: SourceError) -> finish_up Nothing (srcErrorMessages e)) $
        do
          -- TODO: measure time and stop after a phase if it takes too long?
          parsed_mod <- parseModule modsum
          tcd_mod <- typecheckModule parsed_mod
          ds_mod <- desugarModule tcd_mod
          loadModule ds_mod -- ensure it's in the HPT
          finish_up (Just (Typechecked tcd_mod)) mempty

   preprocessModule fname = do
     depanal [] True
     -- reload-calculate the ModSummary because it contains the cached
     -- preprocessed source code
     mb_modsum <- filePathToProjectModule fname
     case mb_modsum of
       Nothing -> error "Huh? No modsummary after preprocessing?"
       Just ms -> return ms

-- | Typechecks a file whose content are given as a string.
backgroundTypecheckArbitrary:: 
       FilePath -- ^ the file path
    -> String -- ^ the file contents
    -> ScionM (Either String CompilationResult)
       -- ^ Error message or compilation result
backgroundTypecheckArbitrary fname contents = do
  mb_modsum <- filePathToProjectModule fname
  case mb_modsum of
    Nothing -> do
      return $ Left "Could not find file in module graph."

    Just modsum -> do
      -- http://hackage.haskell.org/trac/ghc/ticket/3675
      let phase = case (takeExtension fname) of
                ".lhs" -> Just $ Unlit HsSrcFile
                _     -> Nothing
      ghandle (\(e' :: GhcException) -> do
          removeTarget (TargetFile fname phase)
          -- add target without content
          addTarget (Target (TargetFile fname Nothing) False Nothing)
          load LoadAllTargets >>= getDefSiteDB
          throw e') $ do

        let modName = moduleName $ ms_mod modsum
        -- get contents
        sb <- liftIO $ stringToStringBuffer contents
        ct <- liftIO $ getClockTime
        let tgt = TargetFile fname phase
        -- I don't think we use TargetModule anywhere but hey
        removeTarget (TargetModule modName)
        -- remove old target
        removeTarget tgt
        -- add target + content
        addTarget (Target tgt False (Just (sb,ct)))
      
        rslt <- load LoadAllTargets
        getDefSiteDB rslt
        if compilationSucceeded rslt
          then backgroundTypecheckFile fname
          else do
                   return (Right rslt)

-- | Return whether the filepath refers to a file inside the current project
--   root.  Return 'False' if there is no current project.
isRelativeToProjectRoot :: FilePath -> ScionM Bool
isRelativeToProjectRoot fname = do
   root_dir <- projectRootDir
   return (isRelative (makeRelative root_dir fname))
  `gcatch` \(_ :: SomeScionException) -> return False


filePathToProjectModule :: FilePath -> ScionM (Maybe ModSummary)
filePathToProjectModule fname = do
   -- We use the current module graph, don't bother to do a new depanal
   -- if it's empty then we have no current component, hence no BgTcCache.
   --
   -- We check for both relative and absolute filenames because we don't seem
   -- to have any guarantee from GHC what the filenames will look like.
   -- TODO: not sure what happens for names like "../foo"
   root_dir <- projectRootDir
   let rel_fname = normalise (makeRelative root_dir fname)
   mod_graph <- getModuleGraph
   case [ m | m <- mod_graph
            , not (isBootSummary m)
            , Just src <- [ml_hs_file (ms_location m)]
            , src == fname || src == rel_fname || normalise src == normalise rel_fname ]
    of [ m ] -> do return (Just m)
       l     -> do message verbose $ "No module found for " ++ fname ++ (if null l then "" else " reason: ambiguity")
                   return Nothing  -- ambiguous or not present
  `gcatch` \(_ :: SomeScionException) -> return Nothing

isPartOfProject :: FilePath -> ScionM Bool
isPartOfProject fname = fmap isJust (filePathToProjectModule fname)


-- | Ensure that all dependencies of the module are already loaded.
--
-- Sets 'focusedModule' if it was successful.
setContextForBGTC :: ModSummary -> ScionM (Maybe ModuleName, CompilationResult)
setContextForBGTC modsum = do
   message deafening $ "Setting context for: " ++
                       moduleNameString (moduleName (ms_mod modsum))
   let mod_name = ms_mod_name modsum
   start_time <- liftIO $ getCurrentTime
   r <- load (LoadDependenciesOf mod_name) 
           `gcatch` \(e :: SourceError) -> 
               srcErrToCompilationResult start_time e
   modifySessionState $ \sess ->
       sess { focusedModule = if compilationSucceeded r
                               then Just modsum
                               else Nothing
            }
   return (Nothing, r)
  where
    srcErrToCompilationResult start_time err = do
       end_time <- liftIO $ getCurrentTime
       warns <- getWarnings
       clearWarnings
       base_dir <- projectRootDir
       let notes = ghcMessagesToNotes base_dir (warns, srcErrorMessages err)
       return (CompilationResult False notes
                                 (diffUTCTime end_time start_time))
  
-- | Return the 'ModSummary' that refers to the source file.
--
-- Assumes that there is exactly one such 'ModSummary'.
-- 
modSummaryForFile :: FilePath -> ModuleGraph -> ModSummary
modSummaryForFile fname mod_graph =
    case [ m | m <- mod_graph
         , Just src <- [ml_hs_file (ms_location m)]
         , src == fname ]
    of [ m ] -> m
       []    -> dieHard $ "modSummaryForFile: No ModSummary found for " ++ fname
       _     -> dieHard $ "modSummaryForFile: Too many ModSummaries found for "
                          ++ fname


removeMessagesForFile :: AbsFilePath -> CompilationResult -> ScionM CompilationResult
removeMessagesForFile fname res = return res'
  where
    notes = compilationNotes res
    res' = res { compilationNotes = notes' }
    notes' = MS.filter f notes
    f note
      | isValidLoc l, FileSrc fn <- locSource l = fname /= fn
      | otherwise = True
      where l = noteLoc note

-- Local Variables:
-- indent-tabs-mode: nil
-- End:
