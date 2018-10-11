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
    -- * Pretty-printing
    pppIntro,
    pppElim,
#ifdef LANGUAGE_PTS_HAS_NAT
    -- * Natural numbers
    valueNatElim,
#endif
    ) where

import Control.Lens          (review)
import Control.Monad         (ap)
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

-- | 'Value' is in the normal form.
type Value s = ValueIntro Err s Sym

-- | 'ValueIntro' has a normal deduction, \(A\!\uparrow\).
--
-- We assume that all operations are well-typed.
data ValueIntro err s a
    = ValueLam IrrSym (Scope IrrSym (ValueIntro err s) a)
      -- ^ Implication introduction, lambda abstraction.
      --
      -- \[ \frac
      -- {\color{darkblue}{\Gamma^\downarrow, x : \mathord{\tau\!\downarrow}} \vdash \color{darkgreen}b : \color{darkred}{\mathord{\tau'\!\uparrow}}}
      -- {\color{darkblue}{\Gamma^\downarrow} \vdash \color{darkgreen}{\lambda a \to b} : \color{darkred}{\mathord{A \to \tau'\!\uparrow}}}
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

#ifdef LANGUAGE_PTS_HAS_NAT
    | ValueNat
      -- ^ Nat type
    | ValueNatZ
      -- ^ Nat zero
    | ValueNatS (ValueIntro err s a)
      -- ^ Nat successor
#endif

--    | ValueN Natural

--    | ValueReturn (m (ValueIntro err s a))
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

#ifdef LANGUAGE_PTS_HAS_NAT
    -- | Nat elimination
    | ValueNatElim (ValueIntro err s a) (ValueIntro err s a) (ValueIntro err s a) (ValueElim err s a)

-- -   | ValueNatS (ValueElim err s a)
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
    ValueLam n b   >>= k = ValueLam n (b >>>= k)
    ValuePi n a b  >>= k = ValuePi n (a >>= k) (b >>>= k)
    ValueCoerce u  >>= k = valueAppBind u k

    ValueErr err   >>= _ = ValueErr err

#ifdef LANGUAGE_PTS_HAS_NAT
    ValueNat       >>= _ = ValueNat
    ValueNatZ      >>= _ = ValueNatZ
    ValueNatS n    >>= k = ValueNatS (n >>= k)
#endif

--    ValueN n >>= _ = ValueN n

valueAppBind
    :: (PrettyPrec err, AsErr err, Specification s)
    => ValueElim err s a
    -> (a -> ValueIntro err s b)
    -> ValueIntro err s b
valueAppBind (ValueVar a) k = k a
valueAppBind (ValueApp f x) k = case valueAppBind f k of
    ValueCoerce f' -> ValueCoerce (ValueApp f' (x >>= k))
    ValueLam _n f' -> instantiate1 (x >>= k) f'
    ValueErr err   -> ValueErr err
    f'             -> ValueErr $ review _Err $ ApplyPanic (ppp0 (() <$ f'))

#if LANGUAGE_PTS_HAS_NAT
valueAppBind (ValueNatElim a z s n) k = rec (valueAppBind n k)
  where
    rec (ValueCoerce n') = ValueCoerce (ValueNatElim a' z' s' n')
    rec ValueNatZ           = z'
    rec (ValueNatS n')      = valueApp (valueApp s' n') (rec n')
    rec _                = error "panic! valueAppBind ValueNatElim"

    a' = a >>= k
    z' = z >>= k
    s' = s >>= k
#endif

-- valueAppBind (ValueNatS n) k = case valueAppBind n k of
--     ValueCoerce n' -> ValueCoerce (ValueNatS n')
--     ValueN n'      -> ValueN (n' + 1)
--     _              -> error "panic! valueAppBind (ValueNatS _)"

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

#if LANGUAGE_PTS_HAS_NAT
    ValueNatElim a z s n >>= k = ValueNatElim
        (valueBind a k)
        (valueBind z k)
        (valueBind s k)
        (n >>= k)
#endif

#if LANGUAGE_PTS_HAS_FIX
    ValueFix f >>= k = ValueFix (f >>= k)
#endif

--    ValueNatS n >>= k = ValueNatS (n >>= k)

instance (PrettyPrec err, AsErr err, Specification s) => Module (ValueIntro err s) (ValueElim err s) where
    (>>==) = valueBind

-- Module!
valueBind
    :: (PrettyPrec err, AsErr err, Specification s)
    => ValueIntro err s a -> (a -> ValueElim err s b) -> ValueIntro err s b
valueBind (ValueSort s)   _ = ValueSort s
valueBind (ValueCoerce e) k = ValueCoerce (e >>= k)
valueBind (ValueLam n b)  k = ValueLam n (b >>>= ValueCoerce . k)
valueBind (ValuePi n a b) k = ValuePi n (a >>= ValueCoerce . k) (b >>>= ValueCoerce . k)
valueBind (ValueErr err)  _ = ValueErr err

#if LANGUAGE_PTS_HAS_NAT
valueBind ValueNat        _ = ValueNat
valueBind ValueNatZ       _ = ValueNatZ
valueBind (ValueNatS n)   k = ValueNatS (n >>= ValueCoerce . k)
#endif

-- valueBind (ValueN n) _ = ValueN n

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
valueApp f x = do
    b <- ValueCoerce $ ValueApp (ValueVar True) (return False)
    if b then f else x

#if LANGUAGE_PTS_HAS_NAT
valueNatElim
    :: (PrettyPrec err, AsErr err, Specification s)
    => ValueIntro err s a  -- ^ a : (P : Nat) -> *
    -> ValueIntro err s a  -- ^ z : P 0
    -> ValueIntro err s a  -- ^ s : (m : Nat) -> P s -> P (succ m)
    -> ValueIntro err s a  -- ^ n : Nat
    -> ValueIntro err s a  -- ^ _ : P n
valueNatElim a z s n = do
    b <- ValueCoerce $ ValueNatElim
        (return A)
        (return Z)
        (return S)
        (ValueVar N)
    case b of
        A -> a
        Z -> z
        S -> s
        N -> n

data P = A | Z | S | N
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
traverseErrValueIntro f (ValueLam n b)    = ValueLam n <$> transverseScope (traverseErrValueIntro f) b
traverseErrValueIntro f (ValuePi n a b) = ValuePi n
    <$> (traverseErrValueIntro f a)
    <*> (fmap toScope $ traverseErrValueIntro f $ fromScope b)

#ifdef LANGUAGE_PTS_HAS_NAT
traverseErrValueIntro _ ValueNat      = pure ValueNat
traverseErrValueIntro _ ValueNatZ     = pure ValueNatZ
traverseErrValueIntro f (ValueNatS n) = ValueNatS <$> traverseErrValueIntro f n
#endif

traverseErrValueElim :: Applicative f => (err -> f err') -> ValueElim err s a -> f (ValueElim err' s a)
traverseErrValueElim _ (ValueVar a)   = pure (ValueVar a)
traverseErrValueElim f (ValueApp g x) = ValueApp <$> traverseErrValueElim f g <*> traverseErrValueIntro f x

#ifdef LANGUAGE_PTS_HAS_NAT
traverseErrValueElim f (ValueNatElim a z s n) = ValueNatElim
    <$> traverseErrValueIntro f a
    <*> traverseErrValueIntro f z
    <*> traverseErrValueIntro f s
    <*> traverseErrValueElim  f n
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
    liftShowsPrec sp sl d (ValueLam x y) = showsBinaryWith
        showsPrec
        (liftShowsPrec sp sl)
        "ValueLam" d x y
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

#ifdef LANGUAGE_PTS_HAS_NAT
    liftShowsPrec _  _  _ ValueNat      = showString "ValueNat"
    liftShowsPrec _  _  _ ValueNatZ     = showString "ValueNatZ"
    liftShowsPrec sp sl d (ValueNatS x) = showsUnaryWith
        (liftShowsPrec sp sl)
        "ValueNatS" d x
#endif

--    liftShowsPrec _ _ d (ValueN x) = showsUnaryWith
--        showsPrec
--        "ValueN" d x

instance (Show s, Show err) => Show1 (ValueElim err s) where
    liftShowsPrec sp _ d (ValueVar x) =
        showsUnaryWith sp "ValueVar" d x
    liftShowsPrec sp sl d (ValueApp x y) =
        showsBinaryWith (liftShowsPrec sp sl) (liftShowsPrec sp sl) "ValueApp" d x y

#ifdef LANGUAGE_PTS_HAS_NAT
    liftShowsPrec sp sl d (ValueNatElim x y z w) = showsQuadWith
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "ValueNatElim" d x y z w
#endif

--     liftShowsPrec sp sl d (ValueNatS x) = showsUnaryWith
--         (liftShowsPrec sp sl)
--         "ValueVar" d x

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
    liftEq _  (ValueSort s)   (ValueSort s')   = s == s'
    liftEq eq (ValueCoerce x) (ValueCoerce x')  = liftEq eq x x'
    liftEq eq (ValueLam _ x)  (ValueLam _ x')   = liftEq eq x x'
    liftEq eq (ValuePi _ a b) (ValuePi _ a' b') =
        liftEq eq a a' && liftEq eq b b'

    -- Errors are inequal
    liftEq _  (ValueErr _) (ValueErr _) = False

#ifdef LANGUAGE_PTS_HAS_NAT
    liftEq _  ValueNat      ValueNat       = True
    liftEq _  ValueNatZ     ValueNatZ      = True
    liftEq eq (ValueNatS n) (ValueNatS n') = liftEq eq n n'
#endif

    -- catch all case: False
    liftEq _eq _ _ = False

instance Eq s => Eq1 (ValueElim err s) where
    liftEq eq (ValueVar a)   (ValueVar a')    = eq a a'
    liftEq eq (ValueApp f x) (ValueApp f' x') = liftEq eq f f' && liftEq eq x x'

    -- insert
#ifdef LANGUAGE_PTS_HAS_NAT
    liftEq eq (ValueNatElim a z s n) (ValueNatElim a' z' s' n') =
        liftEq eq a a' &&
        liftEq eq z z' &&
        liftEq eq s s' &&
        liftEq eq n n'
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

#ifdef LANGUAGE_PTS_HAS_NAT
pppIntro _ ValueNat  = pppChar 'ℕ'
pppIntro _ ValueNatZ = pppChar '0'
pppIntro d (ValueNatS n)
    | Just n' <- valueIntroToNatural n = pppIntegral $ succ n'
    | otherwise = pppApplication d
        (pppChar 'S')
        [pppIntro PrecApp n]
#endif

pppPeelLam :: (Specification s, PrettyPrec err) => ValueIntro err s Doc -> PrettyM ([Doc], PrettyM Doc)
pppPeelLam (ValueLam n b) = pppScopedIrrSym n $ \nDoc -> do
    ~(xs, ys) <- pppPeelLam (instantiate1return nDoc b)
    return (nDoc : xs, ys)
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
pppPeelPi v = return ([], pppIntro PrecPi v)

instance (Specification s, PrettyPrec err) => PrettyPrec1 (ValueElim err s) where
    liftPpp p d t = traverse (p PrecApp) t >>= pppElim d

pppElim :: (Specification s, PrettyPrec err) => Prec -> ValueElim err s Doc -> PrettyM Doc
pppElim _ (ValueVar a)  = return a
pppElim d t@ValueApp {} = uncurry (pppApplication d) (pppPeelApplication t)

#ifdef LANGUAGE_PTS_HAS_NAT
pppElim d (ValueNatElim a z s n) = pppApplication d
    (pppText "ℕ-elim")
    [ pppIntro PrecApp a
    , pppIntro PrecApp z
    , pppIntro PrecApp s
    , pppElim  PrecApp n
    ]
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

instantiate1return :: a -> Scope IrrSym (ValueIntro err s) a -> ValueIntro err s a
instantiate1return x (Scope s) = fmap k s where
    k (F y) = y
    k (B _) = x

unusedScope :: Traversable m => Scope n m a -> Maybe (m a)
unusedScope (Scope s) = traverse k s where
    k :: Var n a -> Maybe a
    k (F y) = Just y
    k (B _) = Nothing

-------------------------------------------------------------------------------
-- Extension extra
-------------------------------------------------------------------------------

#ifdef LANGUAGE_PTS_HAS_NAT
valueIntroToNatural :: ValueIntro err s a -> Maybe Natural
valueIntroToNatural ValueNatZ     = Just 0
valueIntroToNatural (ValueNatS n) = succ <$> valueIntroToNatural n
valueIntroToNatural _             = Nothing
#endif

-------------------------------------------------------------------------------
-- Extras
-------------------------------------------------------------------------------


{-
-- | Like 'Bound.Scope.bindings' but don't look into 'ValueReturn'.
bindings' :: Scope IrrSym (ValueIntro err s) a -> [Sym]
bindings' (Scope e) = foldMapIntro f e where
    f (B (Name n ())) = [n]
    f _               = []

foldMapIntro :: Monoid r => (a -> r) -> ValueIntro err s a -> r
foldMapIntro _ (ValueSort _)               = mempty
foldMapIntro f (ValueCoerce x)             = foldMapElim f x
foldMapIntro f (ValueLam _ (Scope e))      =
    (foldMapIntro . foldMap . foldMapIntro) f e
foldMapIntro f (ValuePi _ a _ (Scope b) _) = mappend
    (foldMapIntro f a)
    ((foldMapIntro . foldMap . foldMapIntro) f b)

-- foldMapIntro _ (ValueReturn _)            = mempty

foldMapElim :: Monoid r => (a -> r) -> ValueElim err s a -> r
foldMapElim f (ValueVar a) = f a
foldMapElim f (ValueApp g x) = mappend (foldMapElim f g) (foldMapIntro f x)

-- | "Slow" version of @'Bound.Scope.transverseScope' 'errorlessValueElim@ which
-- doesn't require @'Traversable' m@.
runScopeValue
    :: MonadErr m
    => Scope IrrSym (ValueIntro err s) a
    -> m (Scope IrrSym (ValueIntro Void1 s) a)
runScopeValue s = toScope' <$> errorlessValue (fromScope s) where
    toScope' e = Scope (fmap (fmap $ ValueCoerce . ValueVar) e)
-}
