{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings      #-}
-- | Using magic of type-classes we can make...
module Language.PTS.Smart where

import Language.PTS.Bound
import Language.PTS.Specification
import Language.PTS.Sym
import Language.PTS.Term
import Language.PTS.Value

class TermConv t where
    toTermChk   :: t s a -> TermChk s a
    fromTermInf :: TermInf s a -> t s a

instance TermConv TermChk where
    toTermChk   = id
    fromTermInf = Inf

instance TermConv TermInf where
    toTermChk   = Inf
    fromTermInf = id

class ValueConv v where
    toValueIntro :: v err s a -> ValueIntro err s a

instance ValueConv ValueIntro where
    toValueIntro = id

instance ValueConv ValueElim where
    toValueIntro = ValueCoerce

-------------------------------------------------------------------------------
-- Conv
-------------------------------------------------------------------------------

class Convert u v | v -> u where
    convert :: u s a -> v s a

instance Convert TermInf TermInf where convert = id
instance Convert TermInf TermChk where convert = Inf

instance Convert (ValueIntro err) (ValueIntro err) where convert = id

-------------------------------------------------------------------------------
-- App
-------------------------------------------------------------------------------

infixl 3 @@
infixl 3 @@@

class CanApp u v w | w -> u v where
    -- | Left-associative '$' for terms and values.
    (@@) :: u s a -> v s a -> w s a

instance CanApp TermInf TermChk TermInf where
    f @@ x = App f x

instance CanApp TermInf TermChk TermChk where
    f @@ x = Inf (f @@ x)

instance CanApp (ValueElim err) (ValueIntro err) (ValueElim err) where
    f @@ x = ValueApp f x

instance CanApp (ValueElim err) (ValueIntro err) (ValueIntro err) where
    f @@ x = ValueCoerce (f @@ x)

-- | More polymorphic '@@'.
(@@@) :: (TermConv t, TermConv t') => TermInf s a -> t s a -> t' s a
f @@@ x = fromTermInf (App f (toTermChk x))

infixr 1 -:-
infixr 2 ~>

apps_ :: CanApp u v u => u s a -> [v s a] -> u s a
apps_ = foldl (@@)

-------------------------------------------------------------------------------
-- Pi
-------------------------------------------------------------------------------

class Convert u v => CanPi u v | v -> u where
    pi_ :: Sym -> u s Sym -> u s Sym -> v s Sym

    -- | non-dependent function space.
    --
    -- \[
    -- \alpha \to \beta ::= \Pi (- : \alpha). \beta
    -- \]
    (~>) :: (Specification s) => u s a -> u s a -> v s a

#ifdef LANGUAGE_PTS_HAS_SIGMA
    sigma_ :: Sym -> u s Sym -> u s Sym -> v s Sym
#endif

instance CanPi TermInf TermInf where
    pi_ n a b = Pi (IrrSym n) a (abstract1HSym n b)
    a ~> b =
        Pi (IrrSym "_") a (liftH b)

#ifdef LANGUAGE_PTS_HAS_SIGMA
    sigma_ n a b = Sigma (IrrSym n) a (abstract1HSym n b)
#endif

instance CanPi TermInf TermChk where
    pi_ n a b = Inf (Pi (IrrSym n)   a (abstract1HSym n b))
    a ~> b    = Inf (Pi (IrrSym "_") a (liftH b))

#ifdef LANGUAGE_PTS_HAS_SIGMA
    sigma_ n a b = Inf (Sigma (IrrSym n) a (abstract1HSym n b))
#endif

instance CanPi (ValueIntro err) (ValueIntro err) where
    pi_ n a = ValuePi (IrrSym n) a . abstract1Sym n
    -- fix me:
    a ~> b =
        ValuePi (IrrSym "_") a (liftS b)

#ifdef LANGUAGE_PTS_HAS_SIGMA
    sigma_ n a = ValueSigma (IrrSym n) a . abstract1Sym n
#endif

-- | Polymorphic, rank-1 types.
--
-- \[
-- \forall \alpha. F\,\alpha ::= \Pi (\alpha : \star). F\,\alpha
-- \]
forall_ :: (CanPi u v, CanSort u, Specification s) => Sym -> u s Sym -> v s Sym
forall_ a = pi_ a (sort_ typeSort)

foralls_ :: (CanPi u v, CanPi u u, CanSort u, Specification s) => [Sym] -> u s Sym -> v s Sym
foralls_ []     b = convert b
foralls_ (a:as) b = forall_ a (foldr forall_ b as)

-------------------------------------------------------------------------------
-- Sort
-------------------------------------------------------------------------------

class CanSort u where
    sort_ :: s -> u s a

instance CanSort TermChk where
    sort_  = Inf . Sort

instance CanSort TermInf where
    sort_ = Sort

instance CanSort (ValueIntro err) where
    sort_ = ValueSort

-------------------------------------------------------------------------------
-- Lam
-------------------------------------------------------------------------------

class CanLam u where
    lam_ :: Sym -> u s Sym -> u s Sym

instance CanLam TermChk where
    lam_ x@"_" f = Lam (IrrSym x) $ liftH f
    lam_ x f     = Lam (IrrSym x) $ abstract1HSym x f

-- instance CanLam (ValueIntro err) where
--     lam_ x f = ValueLam (IrrSym x) $ abstract1Sym x f

lams_ :: CanLam u => [Sym] -> u s Sym -> u s Sym
lams_ xs t = foldr lam_ t xs

-------------------------------------------------------------------------------
-- Ann
-------------------------------------------------------------------------------

-- | Add annotation only to non-inferrable terms. (So we don't end in @'Ann' ('Inf ('Ann' ...))@ tower.
ann_ :: TermChk s a -> TermInf s a -> TermInf s a
ann_ (Inf a) _ = a
ann_ x       t = Ann x t

(-:-) :: TermChk s a -> TermInf s a -> TermInf s a
(-:-) = ann_

-------------------------------------------------------------------------------
-- Let
-------------------------------------------------------------------------------

-- | Let-bindings.
let_ :: [(Sym, Term s)] -> Term s -> Term s
let_ xs y = foldr f y xs where
    f (n, v) t= t >>= \n' ->
        if n == n'
        then v
        else return n'

infix 0 .=
-- | An alternative name for pair.
(.=) :: a -> b -> (a, b)
(.=) = (,)

-- $setup
-- >>> :set -XOverloadedStrings
