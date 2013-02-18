{-# LANGUAGE CPP #-}
-- |
-- Module      : Scion.Inspect.TypeOf
-- Copyright   : (c) Thomas Schilling 2008
-- License     : BSD-style
--
-- Maintainer  : nominolo@gmail.com
-- Stability   : experimental
-- Portability : portable
--
module Scion.Inspect.TypeOf where

import Scion.Inspect.Find ( SearchResult(..) )

import GHC
import Var ( varType )
import TypeRep ( Type(..), PredType(..) )

------------------------------------------------------------------------------

typeOf :: (SearchResult Id, [SearchResult Id]) -> Maybe Type
typeOf (leaf, path) = case leaf of
   FoundId i -> type_of_id i
   _ -> Nothing
  where
    type_of_id i = case path of
      FoundExpr _ (HsVar _) : FoundExpr _ (HsWrap wr _) : _ ->
          Just $ reduce_type $ unwrap wr (varType i)
      _ -> Just (varType i)

    unwrap WpHole t            = t
    unwrap (WpCompose w1 w2) t = unwrap w1 (unwrap w2 t)
    unwrap (WpCast _) t        = t -- XXX: really?
    unwrap (WpTyApp t') t      = AppTy t t'
    unwrap (WpTyLam tv) t      = ForAllTy tv t
    -- do something else with coercion/dict vars?
    unwrap (WpApp v) t         = AppTy t (TyVarTy v)
    unwrap (WpLam v) t         = ForAllTy v t
    unwrap (WpLet _bs) t       = t
#ifdef WPINLINE
    unwrap WpInline t          = t
#endif

-- | Reduce a top-level type application if possible.  That is, we perform the
-- following simplification step:
-- @
--     (forall v . t) t'   ==>   t [t'/v]
-- @
-- where @[t'/v]@ is the substitution of @t'@ for @v@.
--
reduce_type :: Type -> Type
reduce_type (AppTy (ForAllTy tv b) t) =
    reduce_type (subst_type tv t b)
reduce_type t = t

subst_type :: TyVar -> Type -> Type -> Type
subst_type v t' t0 = go t0
  where
    go t = case t of
      TyVarTy tv 
        | tv == v   -> t'
        | otherwise -> t
      AppTy t1 t2   -> AppTy (go t1) (go t2)
      TyConApp c ts -> TyConApp c (map go ts)
      FunTy t1 t2   -> FunTy (go t1) (go t2)
      ForAllTy v' bt 
        | v == v'   -> t
        | otherwise -> ForAllTy v' (go bt)
      PredTy pt     -> PredTy (go_pt pt)

   -- XXX: this is probably not right
    go_pt (ClassP c ts)  = ClassP c (map go ts)
    go_pt (IParam i t)   = IParam i (go t)
    go_pt (EqPred t1 t2) = EqPred (go t1) (go t2)
