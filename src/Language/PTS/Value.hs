{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UndecidableInstances  #-}
module Language.PTS.Value (
    -- * Values
    Value,
    ValueIntro (..),
    ValueElim (..),
    -- * Combinators
    pureValueIntro,
    pureValueElim,
    mapValueIntroError,
    -- * Application
    valueApp,
    -- * Errors
    errorlessValueIntro,
    errorlessValueIntro',
    errorlessValueElim,
    errorlessValueElim',
#if LANGUAGE_PTS_HAS_SIGMA
    -- * Pairs
    valueMatch,
#endif
#if LANGUAGE_PTS_HAS_EQUALITY
    -- * Equality
    valueJ,
#endif
#if LANGUAGE_PTS_HAS_PROP
    -- * Prop types
    valueAbsurd,
#endif
#if LANGUAGE_PTS_HAS_BOOL
    -- * Booleans
    valueBoolElim,
#if LANGUAGE_PTS_HAS_BOOL_PRIM
    valueAnd,
#endif
#endif
#if LANGUAGE_PTS_HAS_NAT
    -- * Natural numbers
    valueNatElim,
#if LANGUAGE_PTS_HAS_NAT_PRIM
    valuePlus,
    valueTimes,
#endif
#endif
#if LANGUAGE_PTS_HAS_QUARKS
    -- * Quarks
    valueQuarkElim,
#endif
    -- * Pretty-printing
    pppIntro,
    pppElim,
    ) where

import Control.Lens          (review)
import Control.Monad         (ap, void)
import Data.Functor.Classes
import Data.Functor.Identity (Identity (..))
import Data.String           (IsString (..))
import Data.Void             (Void)
import Text.Show.Extras

import Language.PTS.Bound
import Language.PTS.Error
import Language.PTS.Pretty
import Language.PTS.Specification
import Language.PTS.Sym

#ifdef LANGUAGE_PTS_HAS_NAT
import Numeric.Natural
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
import Data.Set (Set)
import Data.Map (Map)

import qualified Data.Set as Set
import qualified Data.Map as Map
#endif

-- | 'Value' is in the normal form.
type Value s = ValueIntro Err s Sym

-- | 'ValueIntro' has a normal deduction, \(A\!\uparrow\).
--
-- We assume that all operations are well-typed.
data ValueIntro err s a
    = ValueLam IrrSym (ValueIntro err s a)  (Scope IrrSym (ValueIntro err s) a)
      -- ^ Implication introduction, lambda abstraction.
      --
      -- \[ \frac
      -- {\color{darkblue}{\Gamma^\downarrow, x : \mathord{\tau\!\downarrow}} \vdash \color{darkgreen}b : \color{darkred}{\mathord{\tau'\!\uparrow}}}
      -- {\color{darkblue}{\Gamma^\downarrow} \vdash \color{darkgreen}{\lambda (a : \tau) \to b} : \color{darkred}{\mathord{\tau \to \tau'\!\uparrow}}}
      -- \]
    | ValueCoerce (ValueElim err s a)
      -- ^ Coercion.
      --
      -- \[ \frac
      -- {\color{darkblue}{\Gamma^\downarrow} \vdash \color{darkgreen}x : \color{darkred}{\mathord{\tau\!\downarrow}}}
      -- {\color{darkblue}{\Gamma^\downarrow} \vdash \color{darkgreen}x : \color{darkred}{\mathord{\tau\!\uparrow}}}
      -- \]
    | ValueSort s
      -- ^ Sort introduction, axiom.
      --
      -- \[ \frac
      -- {s_1 : s_2 \in \mathcal{A}}
      -- {\color{darkblue}{\Gamma^\downarrow} \vdash \color{darkgreen}{s_1} : \color{darkred}{s_2\!\uparrow}}
      -- \]
    | ValuePi IrrSym (ValueIntro err s a) (Scope IrrSym (ValueIntro err s) a)
      -- ^ Function type introduction.
      --
      -- \[ \frac
      -- {(s_1, s_2, s_3 \in \mathcal{S}) \cdots}
      -- {\color{darkblue}{\Gamma^\downarrow} \vdash \cdots}
      -- \]
    | ValueErr err
      -- ^ Falsehood introduction, errors in evaluation, bottoms.
      --
      -- \[ \frac
      -- {\color{darkblue}{\Gamma^\downarrow} \vdash - : \color{darkred}{\bot\!\downarrow}}
      -- {\color{darkblue}{\Gamma^\downarrow} \vdash \color{darkgreen}x : \color{darkred}{\tau\!\uparrow}}
      -- \]

#ifdef LANGUAGE_PTS_HAS_SIGMA
    | ValueSigma IrrSym (ValueIntro err s a) (Scope IrrSym (ValueIntro err s) a)
      -- ^ Dependent pair (sum)

    | ValuePair (ValueIntro err s a) (ValueIntro err s a)
      -- ^ (Dependent) pair constructor
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
    | ValueEquality (ValueIntro err s a) (ValueIntro err s a) (ValueIntro err s a)
      -- ^ Equality

    | ValueRefl
      -- ^ Equality witness
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
    | ValueUnit
    | ValueI
    | ValueEmpty
#endif

#ifdef LANGUAGE_PTS_HAS_BOOL
    | ValueBool
      -- ^ Booleans.
    | ValueTrue
      -- ^ True.
    | ValueFalse
      -- ^ False.
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
    | ValueNat
      -- ^ Nat type
    | ValueNatZ
      -- ^ Nat zero
    | ValueNatS (ValueIntro err s a)
      -- ^ Nat successor
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
    | ValueHadron (Set Sym)
      -- ^ Hadron (collection of quarks) type.

    | ValueQuark Sym
      -- ^ Quark.
#endif

#ifdef LANGUAGE_PTS_HAS_FIXED_POINT
    | ValueMu IrrSym (ValueIntro err s a) (Scope IrrSym (ValueIntro err s) a)
#endif

  deriving (Functor, Foldable, Traversable)

-- | 'ValueElim' is extracted from a hypothesis, \(A\!\downarrow\).
data ValueElim err s a
    = ValueApp (ValueElim err s a) (ValueIntro err s a)
      -- ^ Implication elimination, application.
      --
      -- \[ \frac
      -- {\color{darkblue}{\Gamma^\downarrow} \vdash \color{darkgreen}f      : \color{darkred}{\tau \to \tau'\!\downarrow}  \qquad
      --  \color{darkblue}{\Gamma^\downarrow} \vdash \color{darkgreen}x      : \color{darkred}{\tau\!\uparrow}}
      -- {\color{darkblue}{\Gamma^\downarrow} \vdash \color{darkgreen}{f\,x} : \color{darkred}{\tau'\!\downarrow}}
      -- \]

    | ValueVar a
      -- ^ Hypothesis, variable.
      --
      -- \[ \frac{}
      -- {\color{darkblue}{\Gamma^\downarrow, x : \mathord{\tau\!\downarrow}} \vdash \color{darkgreen}x : \color{darkred}{\tau\!\downarrow}}
      -- \]

#ifdef LANGUAGE_PTS_HAS_SIGMA
    -- | Dependent pattern match on a pair.
    --
    -- @
    -- match p (\x y -> b) ~ (\x y -> b) (fst p) (snd p)
    -- @
    | ValueMatch (ValueElim err s a) IrrSym IrrSym (Scope IrrSym2 (ValueIntro err s) a)
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
      -- | Equality elmination
    | ValueJ (V3 IrrSym)                           -- x y z q
             (ValueIntro err s a)                  -- a : s
             (Scope IrrSym3 (ValueIntro err s) a)  -- P : (x y : a) -> (z : Eq a x y) -> s'
             (ValueIntro err s a)                  -- r : (q : a) -> P q q (refl a q)
             (ValueIntro err s a)                  -- u : a
             (ValueIntro err s a)                  -- v : a
             (ValueElim err s a)                   -- w : Eq a u v
                                                   --   : P u v w
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
    | ValueAbsurd (ValueIntro err s a) (ValueElim err s a)
#endif
 
#ifdef LANGUAGE_PTS_HAS_BOOL
    -- | Boolean elimination
    | ValueBoolElim IrrSym (Scope IrrSym (ValueIntro err s) a) (ValueIntro err s a) (ValueIntro err s a) (ValueElim err s a)

#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM
    -- | Boolean conjunction
    | ValueAnd (ValueElim err s a) (ValueElim err s a)
#endif
#endif


#ifdef LANGUAGE_PTS_HAS_NAT
    -- | Natural number elimination
    | ValueNatElim IrrSym (Scope IrrSym (ValueIntro err s) a) (ValueIntro err s a) (ValueIntro err s a) (ValueElim err s a)

#ifdef LANGUAGE_PTS_HAS_NAT_PRIM
    -- | Natural number addition
    | ValuePlus (ValueElim err s a) (ValueElim err s a)

    -- | Natural number multiplication
    | ValueTimes (ValueElim err s a) (ValueElim err s a)
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
    -- | Hadron elimination.
    | ValueQuarkElim IrrSym (Scope IrrSym (ValueIntro err s) a) (Map Sym (ValueIntro err s a)) (ValueElim err s a)
#endif

#ifdef LANGUAGE_PTS_HAS_FIX
    -- | Fixed point.
    --
    -- \[ \frac
    -- {\color{darkblue}{\Gamma^\downarrow} \vdash \color{darkgreen}{f} : \color{darkred}{\tau \to \tau\!\downarrow}}
    -- {\color{darkblue}{\Gamma^\downarrow} \vdash \color{darkgreen}{\mathsf{fix}\,f} : \color{darkred}{\tau\!\downarrow}}
    -- \]
    | ValueFix (ValueElim err s a)
#endif

  deriving (Functor, Foldable, Traversable)

instance IsString a => IsString (ValueIntro err s a) where
    fromString = ValueCoerce . fromString

instance IsString a => IsString (ValueElim err s a) where
    fromString = ValueVar . fromString

instance (PrettyPrec err, AsErr err, Specification s) => Applicative (ValueIntro err s) where
    pure = pureValueIntro
    (<*>) = ap

instance (PrettyPrec err,  AsErr err, Specification s) => Monad (ValueIntro err s) where
    return = pure

    ValueSort s    >>= _ = ValueSort s
    ValueLam n t b >>= k = ValueLam n (t >>= k) (b >>>= k)
    ValuePi n a b  >>= k = ValuePi n (a >>= k) (b >>>= k)
    ValueCoerce u  >>= k = valueAppBind u k

    ValueErr err   >>= _ = ValueErr err

#ifdef LANGUAGE_PTS_HAS_SIGMA
    ValueSigma x a b >>= k = ValueSigma x (a >>= k) (b >>>= k)
    ValuePair a b    >>= k = ValuePair (a >>= k) (b >>= k)
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
    ValueEquality a x y >>= k = ValueEquality (a >>= k) (x >>= k) (y >>= k)
    ValueRefl           >>= _ = ValueRefl
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
    ValueUnit  >>= _ = ValueUnit
    ValueI     >>= _ = ValueI
    ValueEmpty >>= _ = ValueEmpty
#endif

#ifdef LANGUAGE_PTS_HAS_BOOL
    ValueBool       >>= _ = ValueBool
    ValueTrue       >>= _ = ValueTrue
    ValueFalse      >>= _ = ValueFalse
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
    ValueNat       >>= _ = ValueNat
    ValueNatZ      >>= _ = ValueNatZ
    ValueNatS n    >>= k = ValueNatS (n >>= k)
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
    ValueHadron ls >>= _ = ValueHadron ls
    ValueQuark l   >>= _ = ValueQuark l
#endif

#ifdef LANGUAGE_PTS_HAS_FIXED_POINT
    ValueMu x a b  >>= k = ValueMu x (a >>= k) (b >>>= k)
#endif


valueAppBind
    :: (PrettyPrec err, AsErr err, Specification s)
    => ValueElim err s a
    -> (a -> ValueIntro err s b)
    -> ValueIntro err s b
valueAppBind (ValueVar a) k = k a
valueAppBind (ValueApp f x) k =
    valueApp (valueAppBind f k) (x >>= k)

#ifdef LANGUAGE_PTS_HAS_SIGMA
valueAppBind (ValueMatch p x y b) k = valueMatch
    (valueAppBind p k)
    x y
    (b >>>= k)
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
valueAppBind (ValueJ v3 a p r u v w) k = valueJ v3
    (a >>= k)
    (p >>>= k)
    (r >>= k)
    (u >>= k)
    (v >>= k)
    (valueAppBind w k)
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
valueAppBind (ValueAbsurd a x) k = valueAbsurd (a >>= k) (valueAppBind x k)
#endif

#ifdef LANGUAGE_PTS_HAS_BOOL
valueAppBind (ValueBoolElim x p t f b) k =
    valueBoolElim x (p >>>= k) (t >>= k) (f >>= k) (valueAppBind b k)

#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM
valueAppBind (ValueAnd x y) k =
    valueAnd (valueAppBind x k) (valueAppBind y k)
#endif
#endif

#if LANGUAGE_PTS_HAS_NAT
valueAppBind (ValueNatElim x a z s n) k = 
    valueNatElim x (a >>>= k) (z >>= k) (s >>= k) (valueAppBind n k)

#if LANGUAGE_PTS_HAS_NAT_PRIM
valueAppBind (ValuePlus x y) k =
    valuePlus (valueAppBind x k) (valueAppBind y k)
valueAppBind (ValueTimes x y) k =
    valueTimes (valueAppBind x k) (valueAppBind y k)
#endif
#endif

#if LANGUAGE_PTS_HAS_QUARKS
valueAppBind (ValueQuarkElim x p ls l) k =
    valueQuarkElim x (p >>>= k) (fmap (>>= k) ls) (valueAppBind l k)
#endif

#if LANGUAGE_PTS_HAS_FIX
valueAppBind (ValueFix f) k = case valueAppBind f k of
    ValueCoerce f'     -> ValueCoerce (ValueFix f')
    f'@(ValueLam _n b) -> instantiate1 f' b
    ValueErr err       -> ValueErr err
    f'                 -> ValueErr $ review _Err $ ApplyPanic (pppValueIntro 0 f')
#endif

instance (PrettyPrec err, AsErr err, Specification s) => Applicative (ValueElim err s) where
    pure = pureValueElim
    (<*>) = ap

instance (PrettyPrec err, AsErr err, Specification s) => Monad (ValueElim err s) where
    return = pure

    ValueVar x   >>= k = k x
    ValueApp f x >>= k = ValueApp (f >>= k) (valueBind x k)

#ifdef LANGUAGE_PTS_HAS_SIGMA
    ValueMatch p x y b >>= k = ValueMatch (p >>= k) x y
        (valueBindScope b k)
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
    ValueJ v3 a p r u v w >>= k = ValueJ v3
        (valueBind a k)
        (valueBindScope p k)
        (valueBind r k)
        (valueBind u k)
        (valueBind v k)
        (w >>= k)
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
    ValueAbsurd a x >>= k = ValueAbsurd (valueBind a k) (x >>= k)
#endif

#ifdef LANGUAGE_PTS_HAS_BOOL
    ValueBoolElim x a t f b >>= k = ValueBoolElim x
        (valueBindScope a k)
        (valueBind t k)
        (valueBind f k)
        (b >>= k)

#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM
    ValueAnd x y >>= k = ValueAnd (x >>= k) (y >>= k)
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
    ValueNatElim x a z s n >>= k = ValueNatElim x
        (valueBindScope a k)
        (valueBind z k)
        (valueBind s k)
        (n >>= k)

#if LANGUAGE_PTS_HAS_NAT_PRIM
    ValuePlus  x y >>= k = ValuePlus  (x >>= k) (y >>= k)
    ValueTimes x y >>= k = ValueTimes (x >>= k) (y >>= k)
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
    ValueQuarkElim x p ls l >>= k = ValueQuarkElim x
        (valueBindScope p k)
        (fmap (`valueBind` k) ls)
        (l >>= k)
#endif

#ifdef LANGUAGE_PTS_HAS_FIX
    ValueFix f >>= k = ValueFix (f >>= k)
#endif

#if defined(LANGUAGE_PTS_HAS_SIGMA) || defined(LANGUAGE_PTS_HAS_EQUALITY) || defined(LANGUAGE_PTS_HAS_BOOL) || defined(LANGUAGE_PTS_HAS_NAT) || defined(LANGUAGE_PTS_HAS_QUARKS)
valueBindScope
    :: (AsErr err, Specification s, PrettyPrec err)
    => Scope n (ValueIntro err s) a
    -> (a -> ValueElim err s b)
    -> Scope n (ValueIntro err s) b
valueBindScope s k = toScope $ valueBind (fromScope s) $ unvar (return . B) (fmap F . k)
#endif

instance (PrettyPrec err, AsErr err, Specification s) => Module (ValueIntro err s) (ValueElim err s) where
    (>>==) = valueBind

-- Module!
valueBind
    :: (PrettyPrec err, AsErr err, Specification s)
    => ValueIntro err s a -> (a -> ValueElim err s b) -> ValueIntro err s b
valueBind (ValueSort s)    _ = ValueSort s
valueBind (ValueCoerce e)  k = ValueCoerce (e >>= k)
valueBind (ValueLam n t b) k = ValueLam n (valueBind t k) (b >>>= ValueCoerce . k)
valueBind (ValuePi n a b)  k = ValuePi n (a >>= ValueCoerce . k) (b >>>= ValueCoerce . k)
valueBind (ValueErr err)   _ = ValueErr err

#if LANGUAGE_PTS_HAS_SIGMA
valueBind (ValueSigma x a b) k = ValueSigma x (a >>= ValueCoerce . k) (b >>>= ValueCoerce . k)
valueBind (ValuePair a b)    k = ValuePair (a >>= ValueCoerce . k) (b >>= ValueCoerce . k)
#endif

#if LANGUAGE_PTS_HAS_EQUALITY
valueBind (ValueEquality a x y) k = ValueEquality (a >>= ValueCoerce . k) (x >>= ValueCoerce . k) (y >>= ValueCoerce . k)
valueBind ValueRefl             _ = ValueRefl
#endif

#if LANGUAGE_PTS_HAS_PROP
valueBind ValueUnit _  = ValueUnit
valueBind ValueI _     = ValueI
valueBind ValueEmpty _ = ValueEmpty
#endif

#if LANGUAGE_PTS_HAS_BOOL
valueBind ValueBool        _ = ValueBool
valueBind ValueTrue        _ = ValueTrue
valueBind ValueFalse       _ = ValueFalse

#if LANGUAGE_PTS_HAS_BOOL_NAT
valueBInd (ValueAnd x y) k = ValueAnd (x >>= ValueCoerce . k) (y >>= ValueCoerce . k)
#endif
#endif

#if LANGUAGE_PTS_HAS_NAT
valueBind ValueNat        _ = ValueNat
valueBind ValueNatZ       _ = ValueNatZ
valueBind (ValueNatS n)   k = ValueNatS (n >>= ValueCoerce . k)
#endif

#if LANGUAGE_PTS_HAS_QUARKS
valueBind (ValueHadron ls) _ = ValueHadron ls
valueBind (ValueQuark l)   _ = ValueQuark l
#endif

#if LANGUAGE_PTS_HAS_FIXED_POINT
valueBind (ValueMu x a b) k = ValueMu x (valueBind a k) (b >>>= ValueCoerce . k)
#endif

pureValueIntro :: a -> ValueIntro err s a
pureValueIntro = ValueCoerce . pureValueElim

pureValueElim :: a -> ValueElim err s a
pureValueElim = ValueVar

-------------------------------------------------------------------------------
-- Value application
-------------------------------------------------------------------------------

-- | Apply to values.
--
-- Note that '@@' from "Language.PTSmart" module is different
valueApp
    :: (PrettyPrec err, AsErr err, Specification s)
    => ValueIntro err s a  -- ^ f : a -> b
    -> ValueIntro err s a  -- ^ x : a
    -> ValueIntro err s a  -- ^ _ : b
valueApp (ValueCoerce f)    x = ValueCoerce (ValueApp f x)
valueApp (ValueLam _n _t f) x = instantiate1 x f
valueApp (ValueErr err)     _ = ValueErr err
valueApp f'                 _ = ValueErr $ review _Err $ ApplyPanic "apply" $ ppp0 $ void f'

-------------------------------------------------------------------------------
-- Booleans
-------------------------------------------------------------------------------

#if LANGUAGE_PTS_HAS_BOOL
valueBoolElim
    :: (Specification s, AsErr err, PrettyPrec err)
    => IrrSym                             -- ^ x
    -> Scope IrrSym (ValueIntro err s) a  -- ^ P : s
    -> ValueIntro err s a                 -- ^ t : P true
    -> ValueIntro err s a                 -- ^ f : P false
    -> ValueIntro err s a                 -- ^ b : Bool
    -> ValueIntro err s a                 -- ^ P b
valueBoolElim x p t f = go where
    go (ValueCoerce b) = ValueCoerce (ValueBoolElim x p t f b)
    go ValueTrue       = t
    go ValueFalse      = f
    go (ValueErr err)  = ValueErr err
    go b               = ValueErr $ review _Err $
        ApplyPanic "𝔹-elim" $ ppp0 x <+> ppp0 (void t) <+> ppp0 (void f) <+> ppp0 (void b)

#if LANGUAGE_PTS_HAS_BOOL_PRIM
valueAnd
    :: (Specification s, AsErr err, PrettyPrec err)
    => ValueIntro err s a
    -> ValueIntro err s a
    -> ValueIntro err s a
valueAnd ValueTrue  ValueTrue  = ValueTrue
valueAnd ValueTrue  ValueFalse = ValueFalse
valueAnd ValueFalse ValueTrue  = ValueFalse
valueAnd ValueFalse ValueFalse = ValueFalse

valueAnd (ValueErr err) _ = ValueErr err
valueAnd _ (ValueErr err) = ValueErr err

valueAnd ValueTrue  (ValueCoerce y) = ValueCoerce y
valueAnd ValueFalse (ValueCoerce _) = ValueFalse

valueAnd (ValueCoerce x) ValueTrue   = ValueCoerce x
valueAnd (ValueCoerce _)  ValueFalse = ValueFalse

valueAnd (ValueCoerce x) (ValueCoerce y) = ValueCoerce (ValueAnd x y)

valueAnd x y = ValueErr $ review _Err $ ApplyPanic "𝔹-and" $ ppp0 (void x, void y)
#endif
#endif

-------------------------------------------------------------------------------
-- Natural numbers
-------------------------------------------------------------------------------

#if LANGUAGE_PTS_HAS_NAT
valueNatElim
    :: (Specification s, AsErr err, PrettyPrec err)
    => IrrSym                             -- ^ x
    -> Scope IrrSym (ValueIntro err s) a  -- ^ P : s
    -> ValueIntro err s a                 -- ^ z : P 0
    -> ValueIntro err s a                 -- ^ f : (forall l. P l -> P (succ l)
    -> ValueIntro err s a                 -- ^ n :  Nat
    -> ValueIntro err s a                 -- ^ P n
valueNatElim x p z s = go where
    go (ValueCoerce n) = ValueCoerce (ValueNatElim x p z s n)
    go ValueNatZ       = z
    go (ValueNatS n)   = s `valueApp` n `valueApp` go n
    go n'              = ValueErr $ review _Err $ ApplyPanic "ℕ-elim" $ ppp0 (void n')

#if LANGUAGE_PTS_HAS_NAT_PRIM
valuePlus
    :: (Specification s, AsErr err, PrettyPrec err)
    => ValueIntro err s a
    -> ValueIntro err s a
    -> ValueIntro err s a

valuePlus ValueNatZ     m             = m
valuePlus (ValueNatS n) m             = ValueNatS (valuePlus n m)
valuePlus n             ValueNatZ     = n
valuePlus n             (ValueNatS m) = ValueNatS (valuePlus n m)

valuePlus (ValueCoerce n) (ValueCoerce m) = ValueCoerce (ValuePlus n m)

valuePlus (ValueErr err) _ = ValueErr err
valuePlus _ (ValueErr err) = ValueErr err
valuePlus x y = ValueErr $ review _Err $ ApplyPanic "ℕ-plus" $ ppp0 (void x, void y)

valueTimes
    :: (Specification s, AsErr err, PrettyPrec err)
    => ValueIntro err s a
    -> ValueIntro err s a
    -> ValueIntro err s a

valueTimes ValueNatZ     _             = ValueNatZ
valueTimes (ValueNatS n) m             = valuePlus m (valueTimes n m)
valueTimes _             ValueNatZ     = ValueNatZ
valueTimes n             (ValueNatS m) = valuePlus n (valueTimes n m)

valueTimes (ValueCoerce n) (ValueCoerce m) = ValueCoerce (ValueTimes n m)

valueTimes (ValueErr err) _ = ValueErr err
valueTimes _ (ValueErr err) = ValueErr err
valueTimes x y = ValueErr $ review _Err $ ApplyPanic "ℕ-times" $ ppp0 (void x, void y)
#endif
#endif

-------------------------------------------------------------------------------
-- Hadron
-------------------------------------------------------------------------------

#if LANGUAGE_PTS_HAS_QUARKS
valueQuarkElim
    :: (Specification s, AsErr err, PrettyPrec err)
    => IrrSym
    -> Scope IrrSym (ValueIntro err s) a
    -> Map Sym (ValueIntro err s a)
    -> ValueIntro err s a
    -> ValueIntro err s a
valueQuarkElim x p ls = go where
    go (ValueCoerce l) = ValueCoerce (ValueQuarkElim x p ls l)
    go (ValueErr err)  = ValueErr err
    go (ValueQuark l)
        | Just v <- Map.lookup l ls = v
        -- TODO: make better error
        | otherwise = ValueErr $ review _Err $ SomeErr $ show (l, Map.keys ls)
    go l               = ValueErr $ review _Err $
        ApplyPanic "L-elim" $ ppp0 (void l)
#endif

-------------------------------------------------------------------------------
-- Dependent pair
-------------------------------------------------------------------------------

#ifdef LANGUAGE_PTS_HAS_SIGMA
valueMatch
    :: (Specification s, AsErr err, PrettyPrec err)
    => ValueIntro err s a
    -> IrrSym
    -> IrrSym
    -> Scope IrrSym2 (ValueIntro err s) a
    -> ValueIntro err s a
valueMatch (ValuePair a b) _ _ body = instantiate2 a b body
valueMatch (ValueErr err)  _ _ _    = ValueErr err
valueMatch (ValueCoerce p) x y body = ValueCoerce (ValueMatch p x y body)
valueMatch p _ _ _                  = ValueErr $ review _Err $ ApplyPanic "match" $ ppp0 (void p)
#endif

-------------------------------------------------------------------------------
-- Equality
-------------------------------------------------------------------------------

#ifdef LANGUAGE_PTS_HAS_EQUALITY
valueJ 
    :: (Specification s, AsErr err, PrettyPrec err)
    => V3 IrrSym
    -> ValueIntro err s a
    -> Scope IrrSym3 (ValueIntro err s) a
    -> ValueIntro err s a
    -> ValueIntro err s a
    -> ValueIntro err s a
    -> ValueIntro err s a
    -> ValueIntro err s a
valueJ v3 a p r u v w = case w of
    ValueRefl      -> valueApp r u
    ValueErr err   -> ValueErr err
    ValueCoerce w' -> ValueCoerce (ValueJ v3 a p r u v w')
    _              -> ValueErr $ review _Err $ ApplyPanic "j" $ ppp0 (void w)
#endif

-------------------------------------------------------------------------------
-- Prop
-------------------------------------------------------------------------------

#ifdef LANGUAGE_PTS_HAS_PROP
valueAbsurd 
    :: (Specification s, AsErr err, PrettyPrec err)
    => ValueIntro err s a
    -> ValueIntro err s a
    -> ValueIntro err s a
valueAbsurd a (ValueCoerce x) = ValueCoerce (ValueAbsurd a x)
valueAbsurd _ (ValueErr err)  = ValueErr err
valueAbsurd _ v               = ValueErr $ review _Err $ ApplyPanic "absurd" $ ppp0 (void v)
#endif

-------------------------------------------------------------------------------
-- Run values
-------------------------------------------------------------------------------

mapValueIntroError :: (err -> err') -> ValueIntro err s a -> ValueIntro err' s a
mapValueIntroError f = runIdentity . traverseErrValueIntro (Identity . f)

-- | Expose an error if it's there.
traverseErrValueIntro :: Applicative f => (err -> f err') -> ValueIntro err s a -> f (ValueIntro err' s a)
traverseErrValueIntro f (ValueErr err)    = ValueErr <$> f err
traverseErrValueIntro _ (ValueSort s)     = pure (ValueSort s)
traverseErrValueIntro f (ValueCoerce e)   = ValueCoerce <$> traverseErrValueElim f e
traverseErrValueIntro f (ValueLam n t b)  = ValueLam n
    <$> traverseErrValueIntro f t
    <*> transverseScope (traverseErrValueIntro f) b
traverseErrValueIntro f (ValuePi n a b)   = ValuePi n
    <$> traverseErrValueIntro f a
    <*> transverseScope (traverseErrValueIntro f) b

#ifdef LANGUAGE_PTS_HAS_SIGMA
traverseErrValueIntro f (ValueSigma x a b) = ValueSigma x
    <$> traverseErrValueIntro f a
    <*> transverseScope (traverseErrValueIntro f) b
traverseErrValueIntro f (ValuePair a b) = ValuePair
    <$> traverseErrValueIntro f a
    <*> traverseErrValueIntro f b
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
traverseErrValueIntro f (ValueEquality a x y)  = ValueEquality
    <$> traverseErrValueIntro f a
    <*> traverseErrValueIntro f x
    <*> traverseErrValueIntro f y

traverseErrValueIntro _ ValueRefl = pure ValueRefl
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
traverseErrValueIntro _ ValueUnit      = pure ValueUnit
traverseErrValueIntro _ ValueI         = pure ValueI
traverseErrValueIntro _ ValueEmpty     = pure ValueEmpty
#endif

#ifdef LANGUAGE_PTS_HAS_BOOL
traverseErrValueIntro _ ValueBool      = pure ValueBool
traverseErrValueIntro _ ValueTrue      = pure ValueTrue
traverseErrValueIntro _ ValueFalse     = pure ValueFalse
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
traverseErrValueIntro _ ValueNat      = pure ValueNat
traverseErrValueIntro _ ValueNatZ     = pure ValueNatZ
traverseErrValueIntro f (ValueNatS n) = ValueNatS <$> traverseErrValueIntro f n
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
traverseErrValueIntro _ (ValueHadron ls) = pure (ValueHadron ls)
traverseErrValueIntro _ (ValueQuark l)   = pure (ValueQuark l)
#endif


traverseErrValueElim :: Applicative f => (err -> f err') -> ValueElim err s a -> f (ValueElim err' s a)
traverseErrValueElim _ (ValueVar a)   = pure (ValueVar a)
traverseErrValueElim f (ValueApp g x) = ValueApp <$> traverseErrValueElim f g <*> traverseErrValueIntro f x

#ifdef LANGUAGE_PTS_HAS_SIGMA
traverseErrValueElim g (ValueMatch p x y b) = ValueMatch
    <$> traverseErrValueElim g p
    <*> pure x
    <*> pure y
    <*> transverseScope (traverseErrValueIntro g) b
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
traverseErrValueElim g (ValueJ v3 a p r u v w) = ValueJ v3
    <$> traverseErrValueIntro g a
    <*> transverseScope (traverseErrValueIntro g) p
    <*> traverseErrValueIntro g r
    <*> traverseErrValueIntro g u
    <*> traverseErrValueIntro g v
    <*> traverseErrValueElim g w
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
traverseErrValueElim g (ValueAbsurd a x) = ValueAbsurd
    <$> traverseErrValueIntro g a
    <*> traverseErrValueElim g x
#endif

#ifdef LANGUAGE_PTS_HAS_BOOL
traverseErrValueElim g (ValueBoolElim x p t f n) = ValueBoolElim x
    <$> transverseScope (traverseErrValueIntro g) p
    <*> traverseErrValueIntro g t
    <*> traverseErrValueIntro g f
    <*> traverseErrValueElim  g n

#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM
traverseErrValueElim g (ValueAnd x y) = ValueAnd
    <$> traverseErrValueElim g x
    <*> traverseErrValueElim g y
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
traverseErrValueElim f (ValueNatElim x a z s n) = ValueNatElim x
    <$> transverseScope (traverseErrValueIntro f) a
    <*> traverseErrValueIntro f z
    <*> traverseErrValueIntro f s
    <*> traverseErrValueElim  f n

#ifdef LANGUAGE_PTS_HAS_NAT_PRIM
traverseErrValueElim g (ValuePlus x y) = ValuePlus
    <$> traverseErrValueElim g x
    <*> traverseErrValueElim g y

traverseErrValueElim g (ValueTimes x y) = ValueTimes
    <$> traverseErrValueElim g x
    <*> traverseErrValueElim g y
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
traverseErrValueElim f (ValueQuarkElim x p ls l) = ValueQuarkElim x
    <$> transverseScope (traverseErrValueIntro f) p
    <*> traverse (traverseErrValueIntro f) ls
    <*> traverseErrValueElim  f l
#endif

#ifdef LANGUAGE_PTS_HAS_FIX
traverseErrValueElim f (ValueFix g) = ValueFix <$> traverseErrValueElim f g
#endif

errorlessValueIntro :: MonadErr m => ValueIntro Err s a -> m (ValueIntro err' s a)
errorlessValueIntro = traverseErrValueIntro throwErr

errorlessValueElim :: MonadErr m => ValueElim Err s a -> m (ValueElim err' s a)
errorlessValueElim = traverseErrValueElim throwErr

errorlessValueIntro' :: MonadErr m => ValueIntro Err s a -> m (ValueIntro Void s a)
errorlessValueElim'  :: MonadErr m => ValueElim  Err s a -> m (ValueElim Void s a)

errorlessValueIntro' = errorlessValueIntro
errorlessValueElim' = errorlessValueElim

-------------------------------------------------------------------------------
-- Show instances
-------------------------------------------------------------------------------

instance (Show s, Show err) => Show1 (ValueIntro err s) where
    liftShowsPrec sp sl d (ValueLam x y z) = showsTernaryWith
        showsPrec
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "ValueLam" d x y z
    liftShowsPrec sp sl d (ValueCoerce x) = showsUnaryWith
        (liftShowsPrec sp sl)
        "ValueCoerce"
        d x
    liftShowsPrec _ _ d (ValueSort x) = showsUnaryWith
        showsPrec
        "ValueSort" d x
    liftShowsPrec sp sl d (ValuePi x y z) = showsTernaryWith
        showsPrec
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "ValuePi" d x y z
    liftShowsPrec _ _ d (ValueErr err) = showsUnaryWith
        showsPrec
        "ValueErr" d err

#ifdef LANGUAGE_PTS_HAS_SIGMA
    liftShowsPrec sp sl d (ValueSigma x y z) = showsTernaryWith
        showsPrec
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "ValueSigma" d x y z
    liftShowsPrec sp sl d (ValuePair x y) = showsBinaryWith
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "ValuePair" d x y
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
    liftShowsPrec sp sl d (ValueEquality x y z) = showsTernaryWith
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "ValueEquality" d x y z
        
    liftShowsPrec _ _ _ ValueRefl = showString "ValueRefl"
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
    liftShowsPrec _  _  _ ValueUnit  = showString "ValueBool"
    liftShowsPrec _  _  _ ValueI     = showString "ValueI"
    liftShowsPrec _  _  _ ValueEmpty = showString "ValueEmpty"
#endif

#ifdef LANGUAGE_PTS_HAS_BOOL
    liftShowsPrec _  _  _ ValueBool      = showString "ValueBool"
    liftShowsPrec _  _  _ ValueTrue      = showString "ValueTrue"
    liftShowsPrec _  _  _ ValueFalse     = showString "ValueFalse"
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
    liftShowsPrec _  _  _ ValueNat      = showString "ValueNat"
    liftShowsPrec _  _  _ ValueNatZ     = showString "ValueNatZ"
    liftShowsPrec sp sl d (ValueNatS x) = showsUnaryWith
        (liftShowsPrec sp sl)
        "ValueNatS" d x
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
    liftShowsPrec _ _ d (ValueHadron ls) = showsUnaryWith
        showsPrec
        "ValueHadron" d (Set.toList ls)

    liftShowsPrec _ _ d (ValueQuark l) = showsUnaryWith
        showsPrec
        "ValueQuark" d l
#endif

instance (Show s, Show err) => Show1 (ValueElim err s) where
    liftShowsPrec sp _ d (ValueVar x) =
        showsUnaryWith sp "ValueVar" d x
    liftShowsPrec sp sl d (ValueApp x y) =
        showsBinaryWith (liftShowsPrec sp sl) (liftShowsPrec sp sl) "ValueApp" d x y

#ifdef LANGUAGE_PTS_HAS_SIGMA
    liftShowsPrec sp sl d (ValueMatch x y z w) = showsQuadWith
        (liftShowsPrec sp sl)
        showsPrec
        showsPrec
        (liftShowsPrec sp sl)
        "ValueMatch" d x y z w
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
    liftShowsPrec sp sl d (ValueJ v3 a p r u v w) = showParen (d >= 10)
        $ showString "ValueJ"
        . showChar ' ' . showsPrec 11 v3
        . showChar ' ' . liftShowsPrec sp sl 11 a
        . showChar ' ' . liftShowsPrec sp sl 11 p
        . showChar ' ' . liftShowsPrec sp sl 11 r
        . showChar ' ' . liftShowsPrec sp sl 11 u
        . showChar ' ' . liftShowsPrec sp sl 11 v
        . showChar ' ' . liftShowsPrec sp sl 11 w
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
    liftShowsPrec sp sl d (ValueAbsurd x y) = showsBinaryWith
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "ValueAbsurd" d x y
#endif

#ifdef LANGUAGE_PTS_HAS_BOOL
    liftShowsPrec sp sl d (ValueBoolElim x y z w u) = showsQuintWith
        showsPrec
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "ValueBoolElim" d x y z w u

#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM
    liftShowsPrec sp sl d (ValueAnd x y) = showsBinaryWith
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "ValueAnd" d x y
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
    liftShowsPrec sp sl d (ValueNatElim x y z w u) = showsQuintWith
        showsPrec
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "ValueNatElim" d x y z w u

#ifdef LANGUAGE_PTS_HAS_NAT_PRIM
    liftShowsPrec sp sl d (ValuePlus x y) = showsBinaryWith
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "ValuePlus" d x y

    liftShowsPrec sp sl d (ValueTimes x y) = showsBinaryWith
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "ValueTimes" d x y
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
    liftShowsPrec sp sl d (ValueQuarkElim x p ls l) = showsQuadWith
        showsPrec
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "ValueQuarkElim" d x p (P $ Map.toList ls) l
#endif

#ifdef LANGUAGE_PTS_HAS_FIX
    liftShowsPrec sp sl d (ValueFix x) = showsUnaryWith
        (liftShowsPrec sp sl)
        "ValueFix" d x
#endif

instance (Show a, Show err, Show s) => Show (ValueIntro err s a) where showsPrec = showsPrec1
instance (Show a, Show err, Show s) => Show (ValueElim err s a) where showsPrec = showsPrec1

-------------------------------------------------------------------------------
-- Eq instances
-------------------------------------------------------------------------------

instance Eq s => Eq1 (ValueIntro err s) where
    liftEq _  (ValueSort s)     (ValueSort s')     = s == s'
    liftEq eq (ValueCoerce x)   (ValueCoerce x')   = liftEq eq x x'
    liftEq eq (ValueLam _ t x)  (ValueLam _ t' x') =
        liftEq eq x x' && liftEq eq t t'
    liftEq eq (ValuePi _ a b)   (ValuePi _ a' b')  =
        liftEq eq a a' && liftEq eq b b'

    -- Errors are inequal
    liftEq _  (ValueErr _) (ValueErr _) = False

#ifdef LANGUAGE_PTS_HAS_SIGMA
    liftEq eq (ValueSigma _x a b) (ValueSigma _x' a' b') =
        liftEq eq a a' &&
        liftEq eq b b'

    liftEq eq (ValuePair a b) (ValuePair a' b') =
        liftEq eq a a' &&
        liftEq eq b b'
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
    liftEq  eq (ValueEquality a x y) (ValueEquality a' x' y') =
        liftEq eq a a' &&
        liftEq eq x x' &&
        liftEq eq y y'

    liftEq _eq ValueRefl ValueRefl = True
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
    liftEq _ ValueUnit  ValueUnit  = True
    liftEq _ ValueI     ValueI     = True
    liftEq _ ValueEmpty ValueEmpty = True
#endif

#ifdef LANGUAGE_PTS_HAS_BOOL
    liftEq _  ValueBool      ValueBool       = True
    liftEq _  ValueTrue      ValueTrue       = True
    liftEq _  ValueFalse     ValueFalse      = True
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
    liftEq _  ValueNat      ValueNat       = True
    liftEq _  ValueNatZ     ValueNatZ      = True
    liftEq eq (ValueNatS n) (ValueNatS n') = liftEq eq n n'
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
    liftEq _ (ValueHadron ls) (ValueHadron ls') = ls == ls'
    liftEq _ (ValueQuark l)   (ValueQuark l')   = l == l'
#endif

    -- catch all case: False
    liftEq _eq _ _ = False

instance Eq s => Eq1 (ValueElim err s) where
    liftEq eq (ValueVar a)   (ValueVar a')    = eq a a'
    liftEq eq (ValueApp f x) (ValueApp f' x') = liftEq eq f f' && liftEq eq x x'

#ifdef LANGUAGE_PTS_HAS_SIGMA
    liftEq eq (ValueMatch p _ _ b) (ValueMatch p' _ _ b') =
        liftEq eq p p' &&
        liftEq eq b b'
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
    liftEq eq (ValueJ _ a p r x y z) (ValueJ _ a' p' r' x' y' z') =
        liftEq eq a a' &&
        liftEq eq p p' &&
        liftEq eq r r' &&
        liftEq eq x x' &&
        liftEq eq y y' &&
        liftEq eq z z'
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
    liftEq eq (ValueAbsurd a x) (ValueAbsurd a' x') =
        liftEq eq a a' &&
        liftEq eq x x'
#endif


#ifdef LANGUAGE_PTS_HAS_BOOL
    liftEq eq (ValueBoolElim _ p t f b) (ValueBoolElim _ p' t' f' b') =
        liftEq eq p p' &&
        liftEq eq t t' &&
        liftEq eq f f' &&
        liftEq eq b b'

#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM
    liftEq eq (ValueAnd x y) (ValueAnd x' y') =
        liftEq eq x x' &&
        liftEq eq y y'
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
    liftEq eq (ValueNatElim _ a z s n) (ValueNatElim _ a' z' s' n') =
        liftEq eq a a' &&
        liftEq eq z z' &&
        liftEq eq s s' &&
        liftEq eq n n'

#ifdef LANGUAGE_PTS_HAS_NAT_PRIM
    liftEq eq (ValuePlus x y) (ValuePlus x' y') =
        liftEq eq x x' &&
        liftEq eq y y'

    liftEq eq (ValueTimes x y) (ValueTimes x' y') =
        liftEq eq x x' &&
        liftEq eq y y'
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
    liftEq eq (ValueQuarkElim _ p ls l) (ValueQuarkElim _ p' ls' l') =
        liftEq eq p p' &&
        liftEq (liftEq eq) ls ls' &&
        liftEq eq l l'
#endif
        
    -- catch all case: False
    liftEq _eq _ _ = False

instance (Eq a, Eq s) => Eq (ValueIntro err s a) where (==) = eq1
instance (Eq a, Eq s) => Eq (ValueElim err s a) where (==) = eq1

-------------------------------------------------------------------------------
-- PrettyPrec instances
-------------------------------------------------------------------------------

instance (Specification s, PrettyPrec err) => PrettyPrec1 (ValueIntro err s) where
    liftPpp p d t = traverse (p PrecApp) t >>= pppIntro d

pppIntro :: forall err s. (Specification s, PrettyPrec err) => Prec -> ValueIntro err s Doc -> PrettyM Doc
pppIntro d (ValueCoerce x) = pppElim d x
pppIntro d (ValueSort s)   = ppp d s
pppIntro d (ValueErr e)    = ppp d e
pppIntro d v@ValueLam {}   = uncurry (pppLambda d) =<< pppPeelLam v
pppIntro d v@ValuePi {}    = uncurry (pppPi d) =<< pppPeelPi v

#ifdef LANGUAGE_PTS_HAS_EQUALITY
pppIntro d (ValueEquality a x y) = pppApplication d
    "Eq"
    [ pppIntro PrecApp a
    , pppIntro PrecApp x
    , pppIntro PrecApp y
    ]

pppIntro _ ValueRefl = "refl"
#endif

#ifdef LANGUAGE_PTS_HAS_SIGMA
-- TODO: non dependent case
pppIntro d v@ValueSigma {} = uncurry (pppPi d) =<< pppPeelPi v

pppIntro d (ValuePair a b) = pppApplication d
    "pair"
    [ pppIntro PrecApp a
    , pppIntro PrecApp b
    ]
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
pppIntro _ ValueUnit  = pppChar '⊤'
pppIntro _ ValueI     = pppChar 'I'
pppIntro _ ValueEmpty = pppChar '⊥'
#endif

#ifdef LANGUAGE_PTS_HAS_BOOL
pppIntro _ ValueBool  = pppChar '𝔹'
pppIntro _ ValueTrue  = pppText "true"
pppIntro _ ValueFalse = pppText "false"
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
pppIntro _ ValueNat  = pppChar 'ℕ'
pppIntro _ ValueNatZ = pppChar '0'
pppIntro d (ValueNatS n)
    | Just n' <- valueIntroToNatural n = pppIntegral $ succ n'
    | otherwise = pppApplication d
        (pppChar 'S')
        [pppIntro PrecApp n]
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
pppIntro _ (ValueHadron ls) = pppHadron ls
pppIntro _ (ValueQuark l)   = pppQuark l
#endif


pppPeelLam :: (Specification s, PrettyPrec err) => ValueIntro err s Doc -> PrettyM ([Doc], PrettyM Doc)
pppPeelLam (ValueLam n t b) = pppScopedIrrSym n $ \nDoc -> do
    ~(xs, ys) <- pppPeelLam (instantiate1return nDoc b)
    ntDoc <- pppAnnotation PrecAnn (return nDoc) (pppIntro PrecAnn t)
    return (ntDoc : xs, ys)
pppPeelLam v = return ([], pppIntro PrecLambda v)

pppPeelPi :: (PrettyPrec err, Specification s) => ValueIntro err s Doc -> PrettyM ([PPPi], PrettyM Doc)
pppPeelPi (ValuePi n a b)
    | Just b' <- unusedScope b = do
        ~(xs, ys) <- pppPeelPi b'
        return (PPArrow (pppIntro PrecPi a) : xs, ys)
    | ValueSort a' <- a, a' == typeSort =
        pppScopedIrrSym n $ \nDoc -> do
            ~(xs, ys) <- pppPeelPi (instantiate1return nDoc b)
            return (PPForall nDoc : xs, ys)
    | otherwise =
        pppScopedIrrSym n $ \nDoc -> do
            ~(xs, ys) <- pppPeelPi (instantiate1return nDoc b)
            return (PPPi nDoc (pppIntro PrecPi a) : xs, ys)
#ifdef LANGUAGE_PTS_HAS_SIGMA
pppPeelPi (ValueSigma n a b)
    -- TODO: non-dependent product
    | ValueSort a' <- a, a' == typeSort =
        pppScopedIrrSym n $ \nDoc -> do
            ~(xs, ys) <- pppPeelPi (instantiate1return nDoc b)
            return (PPExists nDoc : xs, ys)
    | otherwise =
        pppScopedIrrSym n $ \nDoc -> do
            ~(xs, ys) <- pppPeelPi (instantiate1return nDoc b)
            return (PPSigma nDoc (pppIntro PrecPi a) : xs, ys)
#endif
pppPeelPi v = return ([], pppIntro PrecPi v)

instance (Specification s, PrettyPrec err) => PrettyPrec1 (ValueElim err s) where
    liftPpp p d t = traverse (p PrecApp) t >>= pppElim d

pppElim :: (Specification s, PrettyPrec err) => Prec -> ValueElim err s Doc -> PrettyM Doc
pppElim _ (ValueVar a)  = return a
pppElim d t@ValueApp {} = uncurry (pppApplication d) (pppPeelApplication t)

#ifdef LANGUAGE_PTS_HAS_SIGMA
pppElim d (ValueMatch p x y b) = pppApplication d
    (pppText "match")
    [ pppElim PrecApp p
    , pppScopedIrrSym x $ \xDoc -> pppScopedIrrSym y $ \yDoc ->
        pppLambda PrecApp [xDoc, yDoc] $ pppIntro PrecLambda $ instantiate2return xDoc yDoc b
    ]
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
pppElim d (ValueJ (V3 x y z) a p r u v w) = pppApplication d
    (pppText "J")
    [ pppIntro PrecApp a
    , pppScopedIrrSym x $ \xDoc ->
      pppScopedIrrSym y $ \yDoc ->
      pppScopedIrrSym z $ \zDoc ->
      pppLambda PrecApp [xDoc,yDoc,zDoc] $ pppIntro PrecLambda $ instantiate3return xDoc yDoc zDoc p
    , pppIntro PrecApp r
    , pppIntro PrecApp u
    , pppIntro PrecApp v
    , pppElim PrecApp w
    ]
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
pppElim d (ValueAbsurd a x) = pppApplication d
    (pppText "absurd-as") [ pppIntro PrecApp a, pppElim PrecApp x ]
#endif

#ifdef LANGUAGE_PTS_HAS_BOOL
pppElim d (ValueBoolElim x p t f b) = pppApplication d
    (pppText "𝔹-elim")
    [ pppScopedIrrSym x $ \xDoc -> pppLambda PrecApp [xDoc] $ pppIntro PrecLambda $ instantiate1return xDoc p  -- TODO
    , pppIntro PrecApp t
    , pppIntro PrecApp f
    , pppElim  PrecApp b
    ]

#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM
pppElim d (ValueAnd x y) = pppApplication d
    (pppText "𝔹-and")
    [ pppElim PrecApp x
    , pppElim PrecApp y
    ]
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
pppElim d (ValueNatElim x a z s n) = pppApplication d
    (pppText "ℕ-elim")
    [ pppScopedIrrSym x $ \xDoc -> pppLambda PrecApp [xDoc] $ pppIntro PrecLambda $ instantiate1return xDoc a
    , pppIntro PrecApp z
    , pppIntro PrecApp s
    , pppElim  PrecApp n
    ]

#ifdef LANGUAGE_PTS_HAS_NAT_PRIM
pppElim d (ValuePlus x y) = pppApplication d
    (pppText "ℕ-plus")
    [ pppElim PrecApp x
    , pppElim PrecApp y
    ]

pppElim d (ValueTimes x y) = pppApplication d
    (pppText "ℕ-times")
    [ pppElim PrecApp x
    , pppElim PrecApp y
    ]
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
pppElim d (ValueQuarkElim x p qs q) = pppQuarkElim d x 
    (\xDoc -> pppIntro PrecLambda $ instantiate1return xDoc p)
    (fmap (pppIntro PrecApp) qs)
    (pppElim PrecApp q)
#endif

#ifdef LANGUAGE_PTS_HAS_FIX
pppElim d (ValueFix f) = pppApplication d
    (pppText "fix") [pppIntro PrecApp f]
#endif

pppPeelApplication :: (Specification s, PrettyPrec err) => ValueElim err s Doc -> (PrettyM Doc, [PrettyM Doc])
pppPeelApplication (ValueApp f x) =
    let ~(f', xs) = pppPeelApplication f
    in (f', xs ++ [pppIntro PrecApp x])
pppPeelApplication v = (pppElim PrecApp v, [])

instance (Specification s, PrettyPrec err, PrettyPrec a) => PrettyPrec (ValueIntro err s a) where ppp = ppp1
instance (Specification s, PrettyPrec err, PrettyPrec a) => PrettyPrec (ValueElim err s a)  where ppp = ppp1

-------------------------------------------------------------------------------
-- Extension extra
-------------------------------------------------------------------------------

#ifdef LANGUAGE_PTS_HAS_NAT
valueIntroToNatural :: ValueIntro err s a -> Maybe Natural
valueIntroToNatural ValueNatZ     = Just 0
valueIntroToNatural (ValueNatS n) = succ <$> valueIntroToNatural n
valueIntroToNatural _             = Nothing
#endif
