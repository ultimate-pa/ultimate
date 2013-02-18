-- |
-- Module      : Scion
-- Copyright   : (c) Thomas Schilling 2008
-- License     : BSD-style
--
-- Maintainer  : nominolo@gmail.com
-- Stability   : experimental
-- Portability : portable
--
-- Scion is a library on top of the GHC API to provide IDE-like functionality.
--
module Scion 
  ( ScionM
  , liftIO, MonadIO
  , module Scion  -- re-export full module at least for now
  , module Scion.Session
  , module Scion.Utils
  , module Scion.Cabal
  ) where

import Scion.Types
import Scion.Session
import Scion.Cabal
import Scion.Utils

import GHC
import FastString ( fsLit )
import Outputable ( printSDoc, defaultErrStyle, ppr, (<+>), text )
import GHC.Paths ( libdir )

import Control.Monad ( forM_ )

-- | Run the 'ScionM' monad.
runScion :: ScionM a -> IO a
runScion m = do
  runGhc (Just libdir) $ do
    dflags <- getSessionDynFlags
    r <- liftIO $ mkSessionState dflags
    _ <- setSessionDynFlags (initialScionDynFlags dflags)
    unScionM m r

-- | Run the session with the given static flags.
--
-- Static flags cannot be changed during a session and can only be set once
-- per /process/.  That is, any session running in the same process
-- (i.e. program) must not attempt to set the static flags again.
--
-- Which flags are static flags depends on the version of GHC.
runScion' :: [String] -> ScionM a -> IO a
runScion' static_flags act = do
  let fname = fsLit "<api-client>"
      lflags = [ L (mkSrcSpan (mkSrcLoc fname line 0) (mkSrcLoc fname line (length s))) s
                | (s,line) <- zip static_flags [1..] ]
  (_leftovers, warnings) <- parseStaticFlags lflags
  forM_ warnings $ \(L region msg) ->
    printSDoc (ppr region <+> text msg) defaultErrStyle
  runScion act
