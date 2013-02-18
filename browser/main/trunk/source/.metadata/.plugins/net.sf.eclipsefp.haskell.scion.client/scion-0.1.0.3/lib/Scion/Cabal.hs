{-# LANGUAGE DeriveDataTypeable, ScopedTypeVariables, CPP #-}
-- |
-- Module      : Scion.Cabal
-- Copyright   : (c) Thomas Schilling 2008
-- License     : BSD-style
-- 
-- Maintainer  : nominolo@gmail.com
-- Stability   : experimental
-- Portability : portable
-- 
-- Cabal-related functionality.
-- 
module Scion.Cabal 
  ( CabalComponent(..), 
    scionDistDir, cabalProjectComponents,
    cabalConfigurations, preprocessPackage )
  where

import Scion.Types

import Exception
import GHC hiding ( load )
import GHC.Paths  ( ghc, ghc_pkg )
import Data.Typeable ()

import Text.JSON

import Control.Monad
import Data.Data
import Data.List        ( intercalate )
import Data.Maybe
import System.Directory ( doesFileExist, getDirectoryContents,
                          getModificationTime )
import System.FilePath ( (</>), dropFileName, takeExtension,dropExtension,(<.>) )
import System.Exit ( ExitCode(..) )

import qualified Distribution.ModuleName as PD
                       ( ModuleName, components )
import Distribution.Simple.Configure
import Distribution.Simple.GHC ( ghcOptions )
import Distribution.Simple.LocalBuildInfo hiding ( libdir )
import Distribution.Simple.Build ( initialBuildSteps )
import Distribution.Simple.BuildPaths ( exeExtension )
import Distribution.Simple.PreProcess ( knownSuffixHandlers )
import qualified Distribution.PackageDescription as PD
import qualified Distribution.PackageDescription.Parse as PD
import qualified Distribution.PackageDescription.Configuration as PD

import Distribution.Simple.Configure
import Distribution.PackageDescription.Parse
                        ( readPackageDescription )
import qualified Distribution.Verbosity as V 
                        ( normal, deafening, silent )
import Distribution.Simple.Program 
                        ( defaultProgramConfiguration,
                          userSpecifyPaths )
import Distribution.Simple.Setup 
                        ( defaultConfigFlags, ConfigFlags(..),
                          Flag(..) )

-- * Exception Types
-- also see ScionError Exception 

data CannotOpenCabalProject = CannotOpenCabalProject String
     deriving (Show, Typeable)
instance Exception CannotOpenCabalProject where
  toException  = scionToException
  fromException = scionFromException

data CabalComponent
  = Library FilePath
  | Executable FilePath String
  deriving (Eq, Show)

instance IsComponent CabalComponent where

  componentInit = cabalComponentInit
  componentTargets = cabalTargets
  componentOptions = cabalDynFlags

scionDistDir :: FilePath
scionDistDir = ".dist-scion"

-- | Set up a Cabal component, (re-)configuring it if necessary.
--
-- Checks whether an existing configuration result exists on disk and
-- configures the project if not.  Similarly, if the existing config
-- is outdated the project is reconfigured.
--
cabalComponentInit :: CabalComponent -> ScionM (Maybe String)
cabalComponentInit c = do
  -- TODO: verify that components exist in cabal file
  let cabal_file = cabalFile c
  ok <- io $ doesFileExist cabal_file
  if not ok then return (Just ".cabal file does not exist") else do
   let root_dir = dropFileName cabal_file
   let setup_config = localBuildInfoFile (root_dir </> scionDistDir)
   conf'd <- io $ doesFileExist setup_config
   if not conf'd then do
      message deafening "Configuring: for first time" 
      do_configure root_dir else do
     cabal_time <- io $ getModificationTime cabal_file
     conf_time <- io $ getModificationTime setup_config
     if cabal_time >= conf_time then do
       message deafening "Reconfiguring: .cabal file is newer"
       do_configure root_dir
      else do
        mb_lbi <- io $ maybeGetPersistBuildConfig 
                         (root_dir </> scionDistDir)
        case mb_lbi of
          Nothing -> do
            message deafening "Reconfiguring: Cabal says so"
            do_configure root_dir
          Just _lbi -> do
            setWorkingDir root_dir
            return Nothing
 where
   do_configure root_dir = do
     r <- gtry $ configureCabalProject root_dir scionDistDir []
     case r of
       Left (err :: IOException) -> return (Just (show err))
       Right _ -> return Nothing

cabalFile :: CabalComponent -> FilePath
cabalFile (Library f) = f
cabalFile (Executable f _) = f

-- | Return GHC 'Target's corresponding to this component.
cabalTargets :: CabalComponent -> ScionM [Target]
cabalTargets (Library f) = do
  pd <- cabal_package f
#if CABAL_VERSION < 107
  let modnames = PD.libModules pd
#else
  let modnames | Just lib <- PD.library pd = PD.libModules lib
               | otherwise = []
#endif
  return (map cabalModuleNameToTarget modnames)
cabalTargets (Executable f name) = do
  pd <- cabal_package f
  let ex0 = filter ((name==) . PD.exeName) (PD.executables pd)
  case ex0 of
    [] -> error "no exe" --noExeError n
    (_:_:_) -> error $ "Multiple executables with name: " ++ name
    [exe] -> do
      let proj_root = dropFileName f
      let others = PD.otherModules (PD.buildInfo exe)
      let main_mods =
              [ proj_root </> search_path </> PD.modulePath exe 
              | search_path <- PD.hsSourceDirs (PD.buildInfo exe)]
      existing_main_mods <- filterM (liftIO . doesFileExist) main_mods
      let targets = map (\main_mod -> Target (TargetFile main_mod Nothing) True Nothing) (take 1 existing_main_mods)
             ++
              map cabalModuleNameToTarget others
      return targets

cabal_package :: FilePath -> ScionM PD.PackageDescription   
cabal_package f = do
  let root_dir = dropFileName f
  lbi <- io $ getPersistBuildConfig (root_dir </> scionDistDir)
  return $ localPkgDescr lbi

cabal_build_info :: FilePath -> ScionM LocalBuildInfo
cabal_build_info f = do
  let root_dir = dropFileName f
  io $ getPersistBuildConfig (root_dir </> scionDistDir)

-- | Return command line flags for the component.
cabalDynFlags :: CabalComponent -> ScionM [String]
cabalDynFlags component = do
   lbi <- cabal_build_info (cabalFile component)
   bi <- component_build_info component (localPkgDescr lbi)
   let odir0 = buildDir lbi
   let odir 
         | Executable _ exeName' <- component
           = odir0 </> dropExtension exeName'
         | otherwise
           = odir0
#if CABAL_VERSION < 107
   let opts = ghcOptions lbi bi odir
#else
       clbi
         | Executable _ exeName' <- component
           = fromJust $ lookup exeName' (executableConfigs lbi)
         | otherwise
           = fromJust $ libraryConfig lbi
   let opts = ghcOptions lbi bi clbi odir
#endif
   return $ opts ++ output_file_opts odir
 where
   component_build_info (Library _) pd
     | Just lib <- PD.library pd = return (PD.libBuildInfo lib)
     | otherwise                 = error "no lib" --noLibError
   component_build_info (Executable _ n) pd =
     case [ exe | exe <- PD.executables pd, PD.exeName exe == n ] of
       [ exe ] -> return (PD.buildInfo exe)
       [] -> error "no exe" --noExeError n
       _ -> error $ "Multiple executables, named \"" ++ n ++ 
                    "\" found.  This is weird..."

   output_file_opts odir =
     case component of
       Executable _ exeName' -> 
         ["-o", odir </> exeName' <.>
                  (if null $ takeExtension exeName'
                   then exeExtension
                   else "")]
       _ -> []

-- | Return all components of the specified Cabal file.
-- 
-- Throws:
-- 
--  * 'CannotOpenCabalProject' if an error occurs (e.g., .cabal file
--    does not exist or could not be parsed.).
-- 
cabalProjectComponents :: FilePath -- ^ The .cabal file
                       -> ScionM [Component]
cabalProjectComponents cabal_file = do
  ghandle (\(_ :: ExitCode) ->
                io $ throwIO $ CannotOpenCabalProject cabal_file) $ do
    gpd <- liftIO $ PD.readPackageDescription V.silent cabal_file 
    let pd = PD.flattenPackageDescription gpd
    return $ map Component $
      (if isJust (PD.library pd) then [Library cabal_file] else []) ++
      [ Executable cabal_file (PD.exeName e)
      | e <- PD.executables pd ]


-- returns a list of cabal configurations
-- dist: those who have been configured * /setup-config 
-- config: those from the .scion-config project configuration file
-- all: both
-- uniq: both, but prefer config items
cabalConfigurations :: FilePath -- ^ The .cabal file
                       -> String -- ^ one of "dist" "config" "all"
                       -> Bool -- only show scion default? 
                       -> ScionM [CabalConfiguration]
cabalConfigurations _cabal _type' _scionDefaultOnly = do
  undefined
{-
  let allowed = ["dist", "config", "all", "uniq"]
  when (not $ elem type' allowed) $ scionError $ "invalid value for type, expected: one of " ++ (show allowed)
  let dir = takeDirectory cabal
  existingDists <- liftIO $ filterM (doesFileExist . (\c -> dir </> c </> "setup-config"))
  =<< liftM (filter (not . (`elem` [".", ".."]))) (getDirectoryContents dir)
  config <- parseScionProjectConfig $ projectConfigFileFromDir dir
  let list = (if type' `elem` ["all", "config", "uniq"] then buildConfigurations config else [])
          -- TODO read flags from setup-config files 
          ++ (if type' `elem` ["all", "dist",  "uniq"] then map (\ a-> CabalConfiguration a []) existingDists else [])
  let f = if type' == "uniq" then nubBy (\a b -> distDir a == distDir b) else id
  -- apply filter 
  let list' = f list
  let d = scionDefaultCabalConfig config
  let scionDefault = filter ( ((fromJust d) ==) . distDir) list'
  return $ if isJust d && scionDefaultOnly && (not . null) scionDefault
    then scionDefault
    else list'
-}
-- | Run the steps that Cabal would call before building.
--
-- The main purpose is to run various pre-processors like @c2hs@,
-- @alex@, @happy@, etc.
-- 
preprocessPackage :: FilePath
                  -> ScionM ()
preprocessPackage dist_dir = do
  lbi <- io $ getPersistBuildConfig (localBuildInfoFile dist_dir)
  let pd = localPkgDescr lbi
  io $ initialBuildSteps dist_dir pd lbi V.normal knownSuffixHandlers
  return ()

cabalModuleNameToTarget :: PD.ModuleName -> Target
cabalModuleNameToTarget name =
   Target { targetId = TargetModule (mkModuleName
                                     (cabal_mod_to_string name))
          , targetAllowObjCode = True
          , targetContents = Nothing }
  where
    cabal_mod_to_string m =
        intercalate "." (PD.components m)

-- | Configure a Cabal project using the Cabal library.
-- 
-- This is roughly equivalent to calling "./Setup configure" on the
-- command line.  The difference is that this makes sure to use the
-- same version of Cabal and the GHC API that Scion was built against.
-- This is important to avoid compatibility problems.
-- 
-- If configuration succeeded, sets it as the current project.
-- 
-- TODO: Figure out a way to report more helpful error messages.
-- 
-- Throws:
-- 
--  * 'CannotOpenCabalProject' if configuration failed.
-- 
configureCabalProject :: 
     FilePath -- ^ The project root.  (Where the .cabal file resides)
  -> FilePath -- ^ dist dir, i.e., directory where to put generated
              -- files.
  -> [String] -- ^ command line arguments to "configure". [XXX:
              -- currently ignored!]
  -> ScionM ()
configureCabalProject root_dir dist_dir _extra_args = do
   cabal_file <- find_cabal_file
   gen_pkg_descr <- io $ readPackageDescription V.normal cabal_file
   let prog_conf =
         userSpecifyPaths [("ghc", ghc), ("ghc-pkg", ghc_pkg)]
           defaultProgramConfiguration
   let config_flags = 
         (defaultConfigFlags prog_conf)
           { configDistPref = Flag dist_dir
           , configVerbosity = Flag V.deafening
           , configUserInstall = Flag True
           -- TODO: parse flags properly
           }
   setWorkingDir root_dir
   ghandle (\(e :: IOError) ->
               io $ throwIO $ 
                CannotOpenCabalProject ("Failed to configure: " ++ (show e))) $ do
#if CABAL_VERSION < 107
     lbi <- io $ configure (Left gen_pkg_descr, (Nothing, []))
                           config_flags
#else
     lbi <- io $ configure (gen_pkg_descr, (Nothing, []))
                           config_flags
#endif
     io $ writePersistBuildConfig dist_dir lbi
     io $ initialBuildSteps dist_dir (localPkgDescr lbi) lbi V.normal
                            knownSuffixHandlers

 where
   find_cabal_file = do
      fs <- liftIO $ getDirectoryContents root_dir
      case [ f | f <- fs, takeExtension f == ".cabal" ] of
        [f] -> return $ root_dir </> f
        [] -> io $ throwIO $ CannotOpenCabalProject "no .cabal file"
        _ -> io $ throwIO $ 
               CannotOpenCabalProject "Too many .cabal files"

instance JSON CabalComponent where
  readJSON (JSObject obj)
    | Ok JSNull <- lookupKey obj "library",
      Ok f <- lookupKey obj "cabal-file" =
        return $ Library (fromJSString f)
    | Ok s <- lookupKey obj "executable",
      Ok f <- lookupKey obj "cabal-file" =
        return $ Executable (fromJSString f) (fromJSString s)
  readJSON _ = fail "component"

  showJSON (Library f) =
    makeObject [("library", JSNull),
                ("cabal-file", JSString (toJSString f))]
  showJSON (Executable f n) =
      makeObject [("executable", JSString (toJSString n)),
                  ("cabal-file", JSString (toJSString f))]
