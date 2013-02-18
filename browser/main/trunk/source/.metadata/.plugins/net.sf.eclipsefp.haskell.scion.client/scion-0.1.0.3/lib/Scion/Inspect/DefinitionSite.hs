{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
-- |
-- Module      : Scion.Inspect.DefinitionSite
-- Copyright   : (c) Thomas Schilling 2009
-- License     : BSD-style
--
-- Maintainer  : nominolo@gmail.com
-- Stability   : experimental
-- Portability : portable
--
-- Collecting and finding the definition site of an identifier.
--
-- This module analyses Haskell code to find the definition sites of
-- identifiers within.
--
module Scion.Inspect.DefinitionSite where

import Scion.Types
import Scion.Types.Notes
import Scion.Ghc

import PprTyThing ( pprTyThingInContext )
import TyCon ( isCoercionTyCon, isFamInstTyCon )
import HscTypes ( isBootSummary )

#if GHC_VERSION < 611
import Var ( globalIdVarDetails )
import IdInfo ( GlobalIdDetails(..) )
#else
import Var ( idDetails )
import IdInfo ( IdDetails(..) )
#endif

import qualified Data.Map as M
import Data.List ( foldl' )
import Data.Monoid
import Control.Monad ( foldM )

------------------------------------------------------------------------
-- * Intended Interface

-- | Construct a 'DefSiteDB' for a complete module graph.
--
-- Note: All the modules mentioned in the module graph must have been
-- loaded.  This is done either by a successful call to 'GHC.load' or by a
-- call to 'GHC.loadModule' for each module (in dependency order).
moduleGraphDefSiteDB ::
     FilePath    -- ^ Base path (see 'ghcSpanToLocation')
  -> ModuleGraph
  -> ScionM DefSiteDB
moduleGraphDefSiteDB base_dir mg = do
    let mg' = filter (not . isBootSummary) mg
    foldM go emptyDefSiteDB mg'
  where
    go db modsum = do
      db1 <- moduleSiteDB (base_dir, ms_mod modsum)
      return (db1 `mappend` db)

-- | Construct a 'DefSiteDB' for a single module only.
moduleSiteDB :: (FilePath, Module) 
                -- ^ Base path (see 'ghcSpanToLocation') and module.
             -> ScionM DefSiteDB
moduleSiteDB (base_dir, mdl) = do
  mb_mod_info <- getModuleInfo mdl
  case mb_mod_info of
    Nothing -> return emptyDefSiteDB
    Just mod_info -> do
      return $ mkSiteDB base_dir (modInfoTyThings mod_info)

-- ** Internal Stuff

-- | Construct a 'SiteDB' from a base directory and a list of 'TyThing's.
mkSiteDB :: FilePath -> [TyThing] -> DefSiteDB
mkSiteDB base_dir ty_things = foldl' go emptyDefSiteDB ty_things
  where
    -- TODO: there's probably more stuff to ignore
    go db (ATyCon tycon) | is_boring_tycon tycon = db -- ignore
    go db (ADataCon datacon) | is_boring_datacon datacon = db
    go db (AnId nm)
      | isDictonaryId nm || not (is_interesting_id nm) = db
    -- don't polute with things for which we have no location
    go db ty_thing | not (isGoodSrcSpan (getSrcSpan ty_thing)) = db
    go db ty_thing =
       addToDB (getOccString ty_thing)
               (ghcSpanToLocation base_dir (getSrcSpan ty_thing))
               ty_thing db

    is_interesting_id ident =
#if GHC_VERSION < 611
      case globalIdVarDetails ident of
        VanillaGlobal -> True
        ClassOpId _ -> True
        RecordSelId {} -> True
        NotGlobalId -> True -- global but not exported
        _ -> False
#else
        case idDetails ident of
          VanillaId -> True
          ClassOpId _ -> True
          RecSelId {} -> True
          _ -> False
#endif

    is_boring_tycon tycon =
        isClassTyCon tycon || isCoercionTyCon tycon || isFamInstTyCon tycon

    is_boring_datacon datacon =
        is_boring_tycon (dataConTyCon datacon)

addToDB :: String -> Location -> TyThing -> DefSiteDB -> DefSiteDB
addToDB nm loc ty_thing (DefSiteDB m) =
    DefSiteDB (M.insertWith (++) nm [(loc,ty_thing)] m)


-- | Dump a definition site DB to stdout. (For debugging purposes.)
dumpDefSiteDB :: DefSiteDB -> String
dumpDefSiteDB (DefSiteDB m) = unlines (map pp (M.assocs m))
  where
    pp (s, l_ty_things) = show s ++ ":\n" ++ unlines
      [ "  " ++ show (viewLoc l) ++ ", " ++ pp_ty_thing t
        | (l, t) <- l_ty_things ]

    pp_ty_thing tt@(AnId ident) =
#if GHC_VERSION < 611
        showSDoc (pprTyThingInContext False tt <+> ppr (globalIdVarDetails ident))
#else
        showSDoc (pprTyThingInContext False tt <+> ppr (idDetails ident))
#endif

    pp_ty_thing (ADataCon dcon) =
        showSDoc (ppr dcon <+> ppr (dataConType dcon))

    pp_ty_thing tt = showSDoc (ppr tt)
