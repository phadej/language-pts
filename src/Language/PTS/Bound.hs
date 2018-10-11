{-# LANGUAGE RankNTypes #-}
-- | Bound "prelude" for "Language.PTS".
module Language.PTS.Bound (
    Bound(..),
    -- * Variable
    Var (..),
    unvar,
    -- * Scope (simple)
    Scope(..),
    fromScope,
    toScope,
    abstract,
    abstract1Sym,
    instantiate1,
    bindings,
    transverseScope,
    liftS,
    -- * ScopeH
    ScopeH (..),
    fromScopeH,
    abstractH,
    abstractHEither,
    abstract1HSym,
    instantiate1H,
    instantiateHEither,
    -- lowerScopeT,
    bindingsH,
    liftH,
    -- * Module
    Module (..),
    ) where

import Bound.Class          (Bound (..))
import Bound.Scope.Simple
       (Scope (..), abstract, bindings, fromScope, instantiate1, toScope,
       transverseScope)
import Bound.ScopeH
       (ScopeH (..), abstractH, abstractHEither, bindingsH, fromScopeH,
       instantiate1H, instantiateHEither)
import Bound.Var            (Var (..), unvar)
import Control.Monad.Module (Module (..))

import Language.PTS.Sym

abstract1Sym :: Functor f => Sym -> f Sym -> Scope IrrSym f Sym
abstract1Sym sym = abstract $ \b ->
    if sym == b
    then Just (IrrSym sym)
    else Nothing
{-# INLINE abstract1Sym #-}

-- | Abstract over a single variable
abstract1HSym :: (Functor f, Monad m) => Sym -> f Sym -> ScopeH IrrSym f m Sym
abstract1HSym sym = abstractH $ \b ->
    if sym == b
    then Just (IrrSym sym)
    else Nothing
{-# INLINE abstract1HSym #-}

liftH :: (Functor f, Monad m) => f a -> ScopeH n f m a
liftH s = ScopeH (fmap (F . return) s)

liftS :: Functor m => m a -> Scope n m a
liftS s = Scope (fmap F s)
