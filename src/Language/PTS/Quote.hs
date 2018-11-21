{-# LANGUAGE FunctionalDependencies #-}
-- | Quotation.
--
-- Take a 'Value' back to 'Term'.
--
-- Or more precisely
--
-- * 'ValueIntro' to 'TermChk'
--
-- * 'ValueElim' to 'TermInf'
--
-- Unlike /LambdaPi/, our 'Value' has 'Eq' instance. Therefore we
-- don't need quotation for type-checker. It's sometimes useful anyway.
--
-- >>> t <- type_ emptyCtx systemfIdentity >>= errorlessValueIntro'
-- >>> prettyPut t
-- ∀ a → a → a
--
-- >>> :t t
-- t :: ValueIntro Void SystemF Sym
--
-- >>> prettyPut (quote_ t)
-- ∀ a → a → a
--
-- >>> :t quote_ t
-- quote_ t :: TermChk SystemF Sym
--
-- >>> check_ emptyCtx (quote_ t) (sort_ SysFStar)
--
module Language.PTS.Quote (Quote (..)) where

import Data.Void (Void, absurd)

import Language.PTS.Bound
import Language.PTS.Smart
import Language.PTS.Specification
import Language.PTS.Term
import Language.PTS.Value

class Quote v t | v -> t, t -> v where
    quote_ :: Specification s => v Void s a -> t s a

instance Quote ValueIntro TermChk where
    quote_ = quoteIntro

instance Quote ValueElim TermInf where
    quote_ = quoteElim

-- TODO: change to ... -> TermInf s a
quoteIntro :: Specification s => ValueIntro Void s a -> TermChk s a
quoteIntro (ValueSort s)    = Inf $ Sort s
quoteIntro (ValueCoerce v)  = Inf $ quoteElim v
quoteIntro (ValueLam n _ b) = Lam n (quoteScope b)
quoteIntro (ValuePi n a b)  = Inf $ Pi n (unsafeChkToInf (quote_ a)) (quoteScopeInf b)
quoteIntro (ValueErr err)   = absurd err

#ifdef LANGUAGE_PTS_HAS_BOOL
quoteIntro ValueBool  = Inf TermBool
quoteIntro ValueTrue  = Inf TermTrue
quoteIntro ValueFalse = Inf TermFalse
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
quoteIntro ValueNat      = Inf TermNat
quoteIntro ValueNatZ     = Inf TermNatZ
quoteIntro (ValueNatS n) = Inf $ TermNatS (quote_ n)
#endif

unsafeChkToInf :: Specification s => TermChk s a -> TermInf s a
unsafeChkToInf (Inf u) = u
unsafeChkToInf t       = Ann t (sort_ star_) -- this can be an `error`

quoteElim :: Specification s => ValueElim Void s a -> TermInf s a
quoteElim (ValueVar a)   = Var a
quoteElim (ValueApp f x) = App (quoteElim f) (quote_ x)

#ifdef LANGUAGE_PTS_HAS_BOOL
quoteElim (ValueBoolElim x p t f b) = TermBoolElim x
    (toScope $ unsafeChkToInf $ quoteIntro $ fromScope p)
    (quote_ t)
    (quote_ f)
    (Inf $ quoteElim b)

#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM
quoteElim (ValueAnd x y) = TermAnd (Inf $ quoteElim x) (Inf $ quoteElim y)
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
quoteElim (ValueNatElim a s z n) = TermNatElim
    (quote_ a)
    (quote_ s)
    (quote_ z)
    (Inf $ quoteElim n)
#endif

#ifdef LANGUAGE_PTS_HAS_FIX
quoteElim (ValueFix _f) = error "TODO: fix"
#endif

quoteScope
    :: Specification s
    => Scope n (ValueIntro Void s) a
    -> ScopeH n (TermChk s) (TermInf s) a
quoteScope x = ScopeH $ fmap (fmap return) (quoteIntro (fromScope x))

quoteScopeInf
    :: Specification s
    => Scope n (ValueIntro Void s) a
    -> ScopeH n (TermInf s) (TermInf s) a
quoteScopeInf x = ScopeH $ fmap (fmap return) (unsafeChkToInf (quoteIntro (fromScope x)))

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> import Language.PTS
-- >>> import Language.PTS.Examples
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Systems
