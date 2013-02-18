{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ExistentialQuantification, DeriveDataTypeable #-}
-- |
-- Module      : Scion.Types
-- Copyright   : (c) Thomas Schilling 2008
-- License     : BSD-style
--
-- Maintainer  : nominolo@gmail.com
-- Stability   : experimental
-- Portability : portable
--
-- Types used throughout Scion. 
--
module Scion.Types 
  ( module Scion.Types
  , liftIO, MonadIO
  ) where

import Scion.Types.Notes
import Scion.Types.ExtraInstances()

import GHC
import HscTypes
import MonadUtils ( liftIO, MonadIO )
import Exception

import Text.JSON

import qualified Data.Map as M
import qualified Data.MultiSet as MS
import Distribution.Simple.LocalBuildInfo
import System.Directory ( setCurrentDirectory, getCurrentDirectory )
import System.FilePath ( normalise, (</>), dropFileName )
import Control.Monad ( when )
import Data.IORef
import Data.Monoid
import Data.Time.Clock  ( NominalDiffTime )
import Data.Typeable
import Control.Exception
import Control.Applicative

------------------------------------------------------------------------------
-- * The Scion Monad and Session State

-- XXX: Can we get rid of some of this maybe stuff?
data SessionState 
  = SessionState {
      scionVerbosity :: Verbosity,
      initialDynFlags :: DynFlags,
        -- ^ The DynFlags as they were when Scion was started.  This is used
        -- to reset flags when opening a new project.  Arguably, the GHC API
        -- should provide calls to reset a session.

      localBuildInfo :: Maybe LocalBuildInfo,
        -- ^ Build info from current Cabal project.

      activeComponent :: Maybe Component,
        -- ^ The current active Cabal component.  This affects DynFlags and
        -- targets.  ATM, we don't support multiple active components.

      lastCompResult :: CompilationResult,

      focusedModule :: Maybe ModSummary,
        -- ^ The currently focused module for background typechecking.

      bgTcCache :: Maybe BgTcCache,
        -- ^ Cached state of the background typechecker.

      defSiteDB :: DefSiteDB,
        -- ^ Source code locations.

      client :: String
        -- ^ can be set by the client. Only used by vim to enable special hack
    }

mkSessionState :: DynFlags -> IO (IORef SessionState)
mkSessionState dflags =
    newIORef (SessionState normal dflags Nothing Nothing mempty Nothing Nothing mempty "")


newtype ScionM a
  = ScionM { unScionM :: IORef SessionState -> Ghc a }

instance Monad ScionM where
  return x = ScionM $ \_ -> return x
  (ScionM ma) >>= fb = 
      ScionM $ \s -> do
        a <- ma s 
        unScionM (fb a) s
  fail msg = dieHard msg

instance Functor ScionM where
  fmap f (ScionM ma) =
      ScionM $ \s -> fmap f (ma s)

instance Applicative ScionM where
  pure a = ScionM $ \_ -> return a
  ScionM mf <*> ScionM ma = 
      ScionM $ \s -> do f <- mf s; a <- ma s; return (f a)

liftScionM :: Ghc a -> ScionM a
liftScionM m = ScionM $ \_ -> m

instance MonadIO ScionM where
  liftIO m = liftScionM $ liftIO m

instance ExceptionMonad ScionM where
  gcatch (ScionM act) handler =
      ScionM $ \s -> act s `gcatch` (\e -> unScionM (handler e) s)
  gblock (ScionM act) = ScionM $ \s -> gblock (act s)
  gunblock (ScionM act) = ScionM $ \s -> gunblock (act s)

instance WarnLogMonad ScionM where
  setWarnings = liftScionM . setWarnings
  getWarnings = liftScionM getWarnings

instance GhcMonad ScionM where
  getSession = liftScionM getSession
  setSession = liftScionM . setSession

io :: MonadIO m => IO a -> m a
io = liftIO

modifySessionState :: (SessionState -> SessionState) -> ScionM ()
modifySessionState f =
    ScionM $ \r -> liftIO $ do s <- readIORef r; writeIORef r $! f s

getSessionState :: ScionM SessionState
getSessionState = ScionM $ \s -> liftIO $ readIORef s

gets :: (SessionState -> a) -> ScionM a
gets sel = getSessionState >>= return . sel

setSessionState :: SessionState -> ScionM ()
setSessionState s' = ScionM $ \r -> liftIO $ writeIORef r s'

------------------------------------------------------------------------------
-- ** Verbosity Levels

data Verbosity
  = Silent
  | Normal
  | Verbose
  | Deafening
  deriving (Eq, Ord, Show, Enum, Bounded)

intToVerbosity :: Int -> Verbosity
intToVerbosity n
  | n < 0                                = minBound
  | n > fromEnum (maxBound :: Verbosity) = maxBound
  | otherwise                            = toEnum n

verbosityToInt :: Verbosity -> Int
verbosityToInt = fromEnum

silent :: Verbosity
silent = Silent

normal :: Verbosity
normal = Normal

verbose :: Verbosity
verbose = Verbose

deafening :: Verbosity
deafening = Deafening

getVerbosity :: ScionM Verbosity
getVerbosity = gets scionVerbosity

setVerbosity :: Verbosity -> ScionM ()
setVerbosity v = modifySessionState $ \s -> s { scionVerbosity = v }

message :: Verbosity -> String -> ScionM ()
message v s = do
  v0 <- getVerbosity
  when (v0 >= v) $ liftIO $ putStrLn s

------------------------------------------------------------------------
-- * Reflection into IO

-- | Reflect a computation in the 'ScionM' monad into the 'IO' monad.
reflectScionM :: ScionM a -> (IORef SessionState, Session) -> IO a
reflectScionM (ScionM f) = \(st, sess) -> reflectGhc (f st) sess

-- | Dual to 'reflectScionM'.  See its documentation.
reifyScionM :: ((IORef SessionState, Session) -> IO a) -> ScionM a
reifyScionM act = ScionM $ \st -> reifyGhc $ \sess -> act (st, sess)

------------------------------------------------------------------------------
-- * Compilation Results

data BgTcCache
  = Parsed ParsedModule
  | Typechecked TypecheckedModule

data CompilationResult = CompilationResult { 
      compilationSucceeded :: Bool,
      compilationNotes     :: MS.MultiSet Note,
      compilationTime      :: NominalDiffTime
    }

instance Monoid CompilationResult where
  mempty = CompilationResult True mempty 0
  mappend r1 r2 =
      CompilationResult 
        { compilationSucceeded = 
              compilationSucceeded r1 && compilationSucceeded r2
        , compilationNotes =
            compilationNotes r1 `MS.union` compilationNotes r2
        , compilationTime = compilationTime r1 + compilationTime r2
        }

------------------------------------------------------------------------------
-- * Exceptions

-- | Any exception raised inside Scion is a subtype of this exception.
data SomeScionException
  = forall e. (Exception e) => SomeScionException e
  deriving Typeable

instance Show SomeScionException where show (SomeScionException e) = show e
instance Exception SomeScionException

scionToException :: Exception e => e -> SomeException
scionToException = toException . SomeScionException

scionFromException :: Exception e => SomeException -> Maybe e
scionFromException x = do
  SomeScionException e <- fromException x
  cast e

-- | A fatal error.  Like 'error' but suggests submitting a bug report.
dieHard :: String -> a
dieHard last_wish = do
   error $ "************** Panic **************\n" ++ 
              last_wish ++ 
              "\nPlease file a bug report at:\n  " ++ bug_tracker_url
  where
    bug_tracker_url = "http://code.google.com/p/scion-lib/issues/list"

------------------------------------------------------------------------------
-- * Others \/ Helpers

-- | Shorthand for 'undefined'.
__ :: a
__ = undefined

-- * Go To Definition

-- | A definition site database.
--
-- This is a map from names to the location of their definition and
-- information about the defined entity.  Note that a name may refer to
-- multiple entities.
--
-- XXX: Currently we use GHC's 'TyThing' data type. However, this probably
-- holds on to a lot of stuff we don't need.  It also cannot be serialised
-- directly.  The reason it's done this way is that wrapping 'TyThing' leads
-- to a lot of duplicated code.  Using a custom type might be useful to have
-- fewer dependencies on the GHC API; however it also creates problems
-- mapping things back into GHC API data structures.  If we do this, we
-- should at least remember the 'Unique' in order to quickly look up the
-- original thing.
newtype DefSiteDB =
  DefSiteDB (M.Map String [(Location,TyThing)])

instance Monoid DefSiteDB where
  mempty = emptyDefSiteDB
  mappend = unionDefSiteDB

-- | The empty 'DefSiteDB'.
emptyDefSiteDB :: DefSiteDB
emptyDefSiteDB = DefSiteDB M.empty

-- | Combine two 'DefSiteDB's.   XXX: check for duplicates?
unionDefSiteDB :: DefSiteDB -> DefSiteDB -> DefSiteDB
unionDefSiteDB (DefSiteDB m1) (DefSiteDB m2) =
    DefSiteDB (M.unionWith (++) m1 m2)

-- | Return the list of defined names (the domain) of the 'DefSiteDB'.
-- The result is, in fact, ordered.
definedNames :: DefSiteDB -> [String]
definedNames (DefSiteDB m) = M.keys m

-- | Returns all the entities that the given name may refer to.
lookupDefSite :: DefSiteDB -> String -> [(Location, TyThing)]
lookupDefSite (DefSiteDB m) key =
  case M.lookup key m of
    Nothing -> []
    Just xs -> xs


-- use this exception for everything else which is not important enough to
-- create a new Exception (kiss) 
-- some more Exception types are defined in Session.hs (TODO?)
data ScionError = ScionError String
     deriving (Show, Typeable)
instance Exception ScionError where
  toException  = scionToException
  fromException = scionFromException
scionError :: String -> ScionM a
scionError = liftIO . throwIO . ScionError

-- will be extended in the future
data CabalConfiguration = CabalConfiguration {
    distDir :: FilePath,
    extraArgs :: [String] -- additional args used to configure the project 
  }

type FileComponentConfiguration =
  ( FilePath, -- rel filepath to config file
    [String] -- set of flags to be used to compile that file  
  )

-- the ScionProjectConfig is a project specific configuration file 
-- The syntax must be simple and human readable. One JSON object per line.
-- Example:
-- { 'type' : 'build-configuration', 'dist-dir' : 'dist-custom', 'extra-args' : [ ] }
-- helperf functions see Utils.hs 
data ScionProjectConfig = ScionProjectConfig {
  buildConfigurations :: [CabalConfiguration],
  fileComponentExtraFlags :: [FileComponentConfiguration],
  scionDefaultCabalConfig :: Maybe String
  }
emptyScionProjectConfig :: ScionProjectConfig
emptyScionProjectConfig = ScionProjectConfig [] [] Nothing

----------------------------------------------------------------------



-- | Sets the current working directory and notifies GHC about the
-- change.
-- 
-- TODO: do we want to adjust certain flags automatically?
setWorkingDir :: FilePath -> ScionM ()
setWorkingDir home = do
  cwd <- liftIO $ getCurrentDirectory
  message deafening $ "Setting working directory: " ++ home ++ " (old: " ++ cwd ++ ")"
  liftIO $ setCurrentDirectory home
  cwd' <- liftIO $ getCurrentDirectory -- to avoid normalisation issues
  when (cwd /= cwd') $ do
    message deafening $ "(Working directory changed.)"
    workingDirectoryChanged



class (Show c, Eq c, JSON c) => IsComponent c where
  componentInit    :: c -> ScionM (Maybe String) --error msg
  componentTargets :: c -> ScionM [Target]
  componentOptions :: c -> ScionM [String]

  componentInit _ = return Nothing

data Component = forall c. IsComponent c => Component c

instance Eq Component where
  Component c1 == Component c2 = show c1 == show c2

instance Show Component where
  show (Component c) = show c

data FileComp = FileComp FilePath deriving (Eq, Show)

instance IsComponent FileComp where
  componentInit (FileComp f) = do
    wd <- liftIO $ getCurrentDirectory
    let dir = normalise $ wd </> dropFileName f
    setWorkingDir dir
    return Nothing

  componentTargets (FileComp f) = do
    return [ Target (TargetFile f Nothing)
                    True
                    Nothing ]
  
  componentOptions (FileComp _f) = do
    --cfg <- io getCurrentDirectory
    -- liftM projectConfigFileFromDir $ 
    --config <- parseScionProjectConfig cfg
    return []
    -- let config = []
    -- return $ fromMaybe [] $ 
    --   lookup (takeFileName f) [] --(fileComponentExtraFlags config)

lookupKey :: JSON a => JSObject JSValue -> String -> Result a
lookupKey = flip valFromObj

makeObject :: [(String, JSValue)] -> JSValue
makeObject = makeObj

instance JSON FileComp where
  readJSON (JSObject obj)
    | Ok s <- lookupKey obj "file" =
        return $ FileComp (fromJSString s)
    | otherwise = fail "cabal file"
  readJSON j = fail $ "filecomp not an object" ++ show j
  showJSON (FileComp n) =
      makeObject [("file", JSString (toJSString n))]

