-- |
-- Module      : Scion.Types.Outlines
-- Copyright   : (c) JP Moresmau 2009
-- License     : BSD-style
--
-- Maintainer  : jp@moresmau.fr
-- Stability   : experimental
-- Portability : portable
--
-- Outline representation of source code
--
module Scion.Types.Outline 
  ( OutlineDef(..),TokenDef(..),
    extractNames,trimLocationFile
  )
where

import GHC
import Scion.Types.Notes

import Data.List ( foldl' )

data OutlineDef = OutlineDef
  { od_name       :: Either Name String,
    od_type       :: String,
    od_loc        :: Location,
    od_block      :: Location,
    od_parentName :: Maybe (Name,String)
  }

data TokenDef = TokenDef {
        td_name :: String,
        td_loc :: Location
    }

extractNames:: [OutlineDef] -> [Name]
extractNames
  = foldl' (\l od -> case od_name od of
	               Left n -> n:l
	               Right _ -> l)
           []

trimLocationFile:: [OutlineDef] -> [OutlineDef]
trimLocationFile =
  map (\d@OutlineDef{ od_loc = l, od_block = b} -> 
           d{ od_loc = trimFile l,
              od_block = trimFile b})
