{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}
-- |
-- Module      : Scion.Inspect.PackageDB
-- Copyright   : (c) Thomas Schilling 2008
-- License     : BSD-style
-- 
-- Maintainer  : nominolo@gmail.com
-- Stability   : experimental
-- Portability : portable
-- 
-- Functionality related to accessing the package database and some
-- related databases that might be generated from the information in
-- the package DB.
-- 
module Scion.Inspect.PackageDB
  ( NameDB, nameDBAddName, emptyNameDB, unionNameDB, unionsNameDB,
    lookupNameDB, deletePrefixNameDB,
    buildNameDB, nameDBAddModule, dumpNameDB, readNameDB, nameDBSize,
    scionNameDBLocation, readOrCreateNameDB
  )
where

import Scion.Types
import qualified GHC as Ghc
import qualified Name as Ghc
import qualified Outputable as Ghc
import qualified Module as Ghc
import qualified Config as Ghc

import qualified Data.ListTrie.Patricia.Map.Enum as PM
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad ( foldM, forM_, when )
import Data.List ( foldl' )
import Data.Binary
import Data.Array.IArray
import Data.Binary.Put ( PutM )
import Data.Monoid
import System.Directory
import System.FilePath ( (</>), dropFileName )

-- * Name Database

-- | A database of names and what modules they are defined in.
--
-- The keys of the database are unqualified names, the values are the
-- modules in which the name is defined.  As a result, looking up a
-- name may return multiple modules.  For example, the (fully
-- qualified) name @Foo.Bar.baz@ defined in package @blub@ will be
-- stored as:
-- 
-- > "baz" -> "blub:Foo.Bar"
-- 
-- In fact, looking up a name not only returns the module in which the
-- name is defined, but also the modules from which it is re-exported.
-- 
-- Note also that a 'Ghc.Module' consists of a versioned package and a
-- module name.  Hence, if the user has multiple versions of the same
-- package installed, their exported names will appear as different
-- entities.
-- 
-- A 'NameDB' has an associated 'Binary' instance, so it can be
-- serialised efficiently.

-- TODO: add type info?
newtype NameDB = NameDB { unNameDB :: PM.TrieMap Char DBItems }
  deriving (Eq)

instance Monoid NameDB where
  mempty = emptyNameDB
  mappend = unionNameDB
  mconcat = unionsNameDB

type DBItems = M.Map Ghc.Module (S.Set Ghc.Module)

emptyNameDB :: NameDB
emptyNameDB = NameDB PM.empty

-- | Add a single name to the 'NameDB'.
-- 
-- The name must be exported, so that it has an associated
-- 'Ghc.Module' in which the actual definition lives.
-- 
nameDBAddName :: 
     Ghc.Module -- ^ Module from which the name was /exported/.  It
                -- might be a re-export, though.
  -> Ghc.Name -- ^ The name.  Must be an exported name.
  -> NameDB -> NameDB
nameDBAddName exporting_mod name (NameDB db) = NameDB db'
  where
    key = Ghc.getOccString name
    mdl = Ghc.nameModule name
    db' = PM.insertWith' ins1 key (M.singleton mdl exp_mods) db
    ins1 = M.unionWith S.union
    exp_mods | exporting_mod == mdl = S.empty
             | otherwise = S.singleton exporting_mod

-- | Combine two 'NameDB's.
unionNameDB :: NameDB -> NameDB -> NameDB
unionNameDB (NameDB db1) (NameDB db2) =
    NameDB (PM.unionWith combine db1 db2)
  where
    combine mp1 mp2 = M.unionWith S.union mp1 mp2

unionsNameDB :: [NameDB] -> NameDB
unionsNameDB dbs = NameDB $ PM.unionsWith combine (map unNameDB dbs)
  where
    combine = M.unionWith S.union

nameDBSize :: NameDB -> Int
nameDBSize (NameDB db) = PM.foldl' my_sum 0 db
  where
    my_sum m acc = M.size m + acc

-- | Look up a string in the NameDB.
-- 
-- Returns a list of pairs where the first component is the defining
-- module of the name and the second component are the modules from
-- which the name is re-exported.
lookupNameDB :: String -> NameDB -> [(Ghc.Module, S.Set Ghc.Module)]
lookupNameDB key (NameDB db) =
  case PM.lookup key db of
    Nothing -> []
    Just m -> M.toList m

-- | Return the 'NameDB' of all items that start with the given
-- prefix.  The prefix is removed from each key.
-- 
-- Note: Returns the /original/ map if none of the keys in the input
-- DB have the given prefix.
deletePrefixNameDB :: String -> NameDB -> NameDB
deletePrefixNameDB key (NameDB db) = NameDB (PM.deletePrefix key db)

-- | Dump the contents of the DB to @stdout@.  For debugging purposes
-- only.
dumpNameDB :: NameDB -> ScionM ()
dumpNameDB (NameDB db) = io $ do
  -- Note: It's in the ScionM monad because we require the
  -- static_flags global vars to be initialised before using Ghc.ppr
  forM_ (PM.toAscList db) $ \(name, mods_set) -> do
    let mods = [ (m, S.toList re_exports)
               | (m, re_exports) <- M.toList mods_set ]
    putStrLn $ name ++ ": " ++ Ghc.showSDoc (Ghc.ppr mods)

-- | Just a simple wrapper for 'decodeFile'.

-- TODO: Can there be any difficulties due to GHC's use of a global
-- symbol table for FastStrings (which are used in Ghc.Module)?  We
-- make sure not to use 'ppr' which depends on static_flags which in
-- turn requires an initialised session.
readNameDB :: FilePath -> ScionM NameDB
readNameDB path = do
  io $ decodeFile path

buildNameDB :: ScionM NameDB
buildNameDB = do
  pkg_db_mods <- Ghc.packageDbModules False
  --io $ putStrLn $ Ghc.showSDoc (Ghc.ppr pkg_db_mods)
  --let pkgs = S.toList . S.fromList $ map Ghc.modulePackageId pkg_db_mods
  --io $ putStrLn $ (Ghc.showSDoc . Ghc.ppr $ pkgs)
  --io $ print (length pkgs, length pkg_db_mods)
  --let base_mods = filter ((=="base") . Ghc.packageIdString . Ghc.modulePackageId) pkg_db_mods
  foldM nameDBAddModule emptyNameDB pkg_db_mods

nameDBAddModule :: NameDB -> Ghc.Module -> ScionM NameDB
nameDBAddModule db mdl = do
  mb_mod_info <- Ghc.getModuleInfo mdl
  case mb_mod_info of
    Nothing -> return db
    Just mod_info -> do
      let names = Ghc.modInfoExports mod_info
      return $! foldl' (flip (nameDBAddName mdl)) db names

-- | Return the path to Scion's name DB.  File or directory may not
-- exist.
scionNameDBLocation :: IO FilePath
scionNameDBLocation = do
  data_dir <- getAppUserDataDirectory "scion"
  return $ data_dir </> ("ghc-" ++ Ghc.cProjectVersion) </> "name_db"

readOrCreateNameDB :: ScionM NameDB
readOrCreateNameDB = do
  loc <- io $ scionNameDBLocation
  -- TODO: Make atomic (open_or_create)
  has_db <- io $ doesFileExist loc
  if has_db then
    -- TODO: Check if it's up to date (and relates to the correct
    -- package DB).  Requires checking the time stamp of all
    -- --package-db=... arguments to the GHC API.
    readNameDB loc
   else 
     createNameDB loc

-- | (Re-)create Name DB; overwrites any existing Name DB.
createNameDB :: FilePath -> ScionM NameDB
createNameDB loc = do
  io $ createDirectoryIfMissing True (dropFileName loc)
  -- userMsg "Building index of all installed packages, this may take a while..."

  -- TODO: Build DB in a separate GHC session which is then thrown
  -- away (or reset the external package state).
  name_db <- buildNameDB
  io $ encodeFile loc name_db
  return name_db

----------------------------------------------------------------------
-- * Serialisation

instance Binary NameDB where
  put = putNameDB
  get = getNameDB

-- TODO: Ideally we would like to create the dictionary of Modules on
-- demand but that doesn't work with the interface that Binary
-- provides.  It would work like this: Writing a Module would look up
-- the current ID assigned to that Module, automatically allocating
-- one if none has been assigned yet.  Finally, we would serialise the
-- dictionary mapping IDs to Modules.  Problems:
--
--  1. We cannot update any state inside the PutM monad.  
--
--  2. Because we'd need the dictionary when reading the DB back, we
--     must be able to find and read the dictionary before reading the
--     payload.  GHC's interface writing code implements this by
--     writing a dummy value and then updating that value to point
--     after the payload.  When reading back, GHC first jumps to the
--     dictionary, reads it, and then jumps back to the reading the
--     payload.  This requires some peek and poke primitives, which
--     are not provided by Data.Binary.
--
-- So, since we expect /writing/ of the NameDB to be a rare operation
-- we do a two-pass process: (1) Traverse the DB and construct the
-- dictionary and write it to the beginning of the file, then (2)
-- write the payload, referring to the dictionary.

-- | A special marker to identify the file type.
scionNameDBMagic :: String
scionNameDBMagic = "ScionNameDB"

-- | The expected version of the file.
scionNameDBVersion :: Int
scionNameDBVersion = 1

-- TODO: use IntMap
data BinDict a = BinDict {-# UNPACK #-} !Int (M.Map a Int)
instance Show (BinDict a) where
  show (BinDict n m) = "BinDict(" ++ show n ++ ")" ++ show (M.elems m)

nameDBModules :: NameDB -> S.Set Ghc.Module
nameDBModules (NameDB db) = PM.foldr f S.empty db
  where
    -- We need to consider re_exports because there may be modules
    -- that contain only re-exports and nothing else.
    f items mods =
      foldr S.insert mods 
        [ m | (orig, re_exports) <- M.toList items
            , m <- orig : S.toList re_exports ]

instance Binary Ghc.PackageId where
  put pid = put (Ghc.packageIdString pid)
  get = Ghc.stringToPackageId `fmap` get

instance Binary Ghc.ModuleName where
  put mn = put (Ghc.moduleNameString mn)
  get = Ghc.mkModuleName `fmap` get
  
nameDBDicts :: S.Set Ghc.Module -> (BinDict Ghc.PackageId, BinDict Ghc.ModuleName)
nameDBDicts all_mods = (pkg_dict, mod_name_dict)
  where
    pkg_dict =
      let ps = [ Ghc.modulePackageId mdl | mdl <- S.toList all_mods ] in
      dictFromList (S.toList (S.fromList ps))
    mod_name_dict =
      let ms = [ Ghc.moduleName mdl | mdl <- S.toList all_mods ] in
      dictFromList (S.toList (S.fromList ms))

dictLookup :: Ord a => a -> BinDict a -> Int
dictLookup a (BinDict _ m) = m M.! a

dictFromList :: Ord a => [a] -> BinDict a
dictFromList l = 
  let m = M.fromList (zip l [0..]) in
  BinDict (M.size m) m

-- ** Writing NameDBs

putNameDB :: NameDB -> Put
putNameDB db = do
  let all_mods = nameDBModules db
  let (pkg_id_dict, mod_name_dict) = nameDBDicts all_mods
  put scionNameDBMagic
  put scionNameDBVersion
  putDict pkg_id_dict
  putDict mod_name_dict
  mod_dict <- putModuleDict pkg_id_dict mod_name_dict all_mods
  putPayload mod_dict db
  
putPayload :: BinDict Ghc.Module -> NameDB -> Put
putPayload mod_dict (NameDB db) = put int_db
  where
    int_db = PM.map f db
    f items = [ to_id main_mod : map to_id (S.toList re_exports)
              | (main_mod, re_exports) <- M.toList items ]
    to_id mdl = dictLookup mdl mod_dict

putDict :: forall a. Binary a => BinDict a -> Put
putDict (BinDict _ mp) = do
  let size = M.size mp
  let as :: Array Int a
      !as = array (0, size - 1) [ (i, a) | (a, i) <- M.toList mp ]
  put as

putModuleDict :: BinDict Ghc.PackageId -> BinDict Ghc.ModuleName
              -> S.Set Ghc.Module -> PutM (BinDict Ghc.Module)
putModuleDict pkg_id_dict mod_name_dict mods = do
  let dict@(BinDict _ mp) = dictFromList (S.toList mods)
  let as :: Array Int (Int, Int)
      as = array (0, M.size mp - 1)
                 [ (i, (dictLookup (Ghc.modulePackageId m) pkg_id_dict,
                        dictLookup (Ghc.moduleName m) mod_name_dict))
                 | (m, i) <- M.toList mp ]
  put as
  return dict

-- ** Reading NameDBs
  
getNameDB :: Get NameDB
getNameDB = do
  magic <- get
  version <- get
  when (magic /= scionNameDBMagic || version /= scionNameDBVersion) $ do
    fail "getNameDB: Not a Name DB or wrong version"
  pkg_id_dict <- getDict
  mod_name_dict <- getDict
  mod_dict <- getModuleDict pkg_id_dict mod_name_dict
  getPayload mod_dict
  --return ({- trace (show mod_dict) $-} NameDB PM.empty)

getPayload :: Array Int Ghc.Module -> Get NameDB
getPayload mod_dict = (NameDB . PM.map reconstruct) `fmap` get
  where
    -- The outer list represents distinct identifiers with the same
    -- name.  The inner list are the indices of the modules.  The
    -- first element is always the defining module, the rest are the
    -- re-exports.
    reconstruct :: [[Int]] -> DBItems
    reconstruct is = M.fromList
      [ (mod_dict ! defined_at, S.fromList (map (mod_dict !) re_exports))
        | (defined_at : re_exports) <- is ]

getModuleDict :: Array Int Ghc.PackageId -> Array Int Ghc.ModuleName
              -> Get (Array Int Ghc.Module)
getModuleDict pkg_id_dict mod_name_dict = do
  raw <- getDict
  return $ amap (\(pid, mn) -> Ghc.mkModule (pkg_id_dict ! pid)
                                            (mod_name_dict ! mn)) raw

getDict :: Binary a => Get (Array Int a)
getDict = get

-- * Helper Instances

instance Show Ghc.PackageId where show pid = Ghc.packageIdString pid
instance Show Ghc.ModuleName where show mn = Ghc.moduleNameString mn
instance Show Ghc.Module where
  show m = show (Ghc.modulePackageId m) ++ ":" ++ show (Ghc.moduleName m)
