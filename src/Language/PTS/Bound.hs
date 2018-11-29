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
    instantiate1return,
    instantiate2,
    instantiate2return,
    instantiate3,
    instantiate3return,
    bindings,
    transverseScope,
    liftS,
    unusedScope,
    -- * ScopeH
    ScopeH (..),
    fromScopeH,
    abstractH,
    abstractHEither,
    abstract1HSym,
    abstract2HSym,
    abstract3HSym,
    instantiate1H,
    instantiate1Hreturn,
    instantiate2H,
    instantiate2Hreturn,
    instantiate3H,
    instantiate3Hreturn,
    instantiateHEither,
    -- lowerScopeT,
    bindingsH,
    liftH,
    -- * Module
    Module (..),
    ) where

import Bound.Class          (Bound (..))
import Bound.Scope.Simple
       (Scope (..), abstract, bindings, fromScope, instantiate, instantiate1,
       toScope, transverseScope)
import Bound.ScopeH
       (ScopeH (..), abstractH, abstractHEither, bindingsH, fromScopeH,
       instantiate1H, instantiateH, instantiateHEither)
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

-- | Abstract over two variables
abstract2HSym :: (Functor f, Monad m) => Sym -> Sym -> f Sym -> ScopeH IrrSym2 f m Sym
abstract2HSym sym1 sym2 = abstractH f where
    f b | b == sym1 = Just (IrrSym1 sym1)
        | b == sym2 = Just (IrrSym2 sym2)
        | otherwise = Nothing

-- | Abstract over tree variables
abstract3HSym :: (Functor f, Monad m) => Sym -> Sym -> Sym -> f Sym -> ScopeH IrrSym3 f m Sym
abstract3HSym sym1 sym2 sym3 = abstractH f where
    f b | b == sym1 = Just (IrrSymI sym1)
        | b == sym2 = Just (IrrSymJ sym2)
        | b == sym3 = Just (IrrSymK sym2)
        | otherwise = Nothing

liftH :: (Functor f, Monad m) => f a -> ScopeH n f m a
liftH s = ScopeH (fmap (F . return) s)

liftS :: Functor m => m a -> Scope n m a
liftS s = Scope (fmap F s)

instantiate1return :: Functor f => a -> Scope IrrSym f a -> f a
instantiate1return x (Scope s) = fmap k s where
    k (F y) = y
    k (B _) = x

instantiate2  :: Monad f => f a -> f a -> Scope IrrSym2 f a -> f a
instantiate2 x y = instantiate (irrSym2fold x y)

instantiate2return :: Functor f => a -> a -> Scope IrrSym2 f a -> f a
instantiate2return x y (Scope s) = fmap k s where
    k (F z)           = z
    k (B (IrrSym1 _)) = x
    k (B (IrrSym2 _)) = y

instantiate3  :: Monad f => f a -> f a -> f a -> Scope IrrSym3 f a -> f a
instantiate3 x y z = instantiate (irrSym3fold x y z)

instantiate3return :: Functor f => a -> a -> a -> Scope IrrSym3 f a -> f a
instantiate3return x y z (Scope s) = fmap k s where
    k (F q)           = q
    k (B (IrrSymI _)) = x
    k (B (IrrSymJ _)) = y
    k (B (IrrSymK _)) = z

instantiate1Hreturn :: Module f m => a -> ScopeH IrrSym f m a -> f a
instantiate1Hreturn x = instantiate1H (return x)

instantiate2H :: Module f m => m a -> m a -> ScopeH IrrSym2 f m a -> f a
instantiate2H x y = instantiateH (irrSym2fold x y)

instantiate2Hreturn :: Module f m => a -> a -> ScopeH IrrSym2 f m a -> f a
instantiate2Hreturn x y = instantiate2H (return x) (return y)

instantiate3H :: Module f m => m a -> m a -> m a -> ScopeH IrrSym3 f m a -> f a
instantiate3H x y z = instantiateH (irrSym3fold x y z)

instantiate3Hreturn :: Module f m => a -> a -> a -> ScopeH IrrSym3 f m a -> f a
instantiate3Hreturn x y z = instantiate3H (return x) (return y) (return z)

unusedScope :: Traversable m => Scope n m a -> Maybe (m a)
unusedScope (Scope s) = traverse k s where
    k :: Var n a -> Maybe a
    k (F y) = Just y
    k (B _) = Nothing
