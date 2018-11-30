module Language.PTS.Value.Check (
    valueType_,
    ) where

import Control.Lens (review)

import Language.PTS.Bound
import Language.PTS.Value
import Language.PTS.Error
import Language.PTS.Pretty
import Language.PTS.Specification

-- | Get a type of 'ValueElim'.
--
-- TODO: implement 'valueType' for 'ValueIntro' too.
valueType_
    :: (Specification s, AsErr err, PrettyPrec err, PrettyPrec a)
    => (a -> Maybe (ValueIntro err s a))
    -> ValueElim err s a
    -> ValueIntro err s a
valueType_ ctx (ValueVar a) = case ctx a of
    Nothing -> ValueErr $ review _Err $ VariableNotInScope (ppp0 a) []
    Just t  -> t
valueType_ ctx (ValueApp f x) = case valueType_ ctx f of
    ValuePi _n _a b -> instantiate1 x b
    ValueErr err    -> ValueErr err
    ft              -> ValueErr $ review _Err $ NotAFunction (ppp0 ft) (ppp0 f) (ppp0 x) []

#ifdef LANGUAGE_PTS_HAS_SIGMA
valueType_ ctx (ValueMatch p _ _ _b) = case valueType_ ctx p of
    -- TODO
    ValueErr err -> ValueErr err
    pt           -> ValueErr $ review _Err $ NotAPair (ppp0 pt) (ppp0 p) []
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
valueType_ _ ValueJ {}
    = ValueErr $ review _Err $ SomeErr "valueJ"
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
valueType_ _ ValueAbsurd {}
    = ValueErr $ review _Err $ SomeErr "valueAbsurd"
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
valueType_ _ ValueQuarkElim {}
    = ValueErr $ review _Err $ SomeErr "valueQuarkElim"
#endif

#ifdef LANGUAGE_PTS_HAS_BOOL
valueType_ _ctx (ValueBoolElim _ p _ _ b) = instantiate1 (ValueCoerce b) p
#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM
valueType_ _ctx (ValueAnd _ _) = ValueBool
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
valueType_ _ctx (ValueNatElim _ p _ _ n) = instantiate1 (ValueCoerce n) p

#ifdef LANGUAGE_PTS_HAS_NAT_PRIM
valueType_ _ctx (ValuePlus _ _)  = ValueNat
valueType_ _ctx (ValueTimes _ _) = ValueNat
#endif
#endif

{-
valueIntroType_
    :: (Specification s, AsErr err, PrettyPrec err, PrettyPrec a)
    => (a -> Maybe (ValueIntro err s a))
    -> ValueIntro err s a
    -> ValueIntro err s a
valueIntroType_ ctx (ValueLam x t b) = ValuePi x t
    $ toScope $ valueIntroType_ (addContext t ctx) $ fromScope b
valueIntroType_ ctx (ValueCoerce x) = valueType_ ctx x
valueIntroType_ _ctx (ValueSort s) = case axiom s of
    Nothing -> ValueErr $ _Err # SortWithoutAxiom (ppp0 s) []
    Just s' -> ValueSort s'
valueIntroType_ ctx (ValuePi _ t b) =
    case valueIntroType_ ctx t of
        ValueSort as  -> case valueIntroType_ (addContext t ctx) (fromScope b) of
            ValueSort bs -> case rule as bs of
                Nothing -> ValueErr $ _Err # NoRule (ppp0 as) (ppp0 bs) []
                Just cs -> ValueSort cs
            ValueErr err -> ValueErr err
            _            -> ValueErr $ _Err # SomeErr "not a sort"
        ValueErr err -> ValueErr err
        _            -> ValueErr $ _Err # SomeErr "not a sort"
valueIntroType_ _ctx (ValueErr err) = ValueErr err
valueIntroType_ _ctx ValueBool = ValueSort typeSort
valueIntroType_ _ctx ValueTrue = ValueBool
valueIntroType_ _ctx ValueFalse = ValueBool
valueIntroType_ _ctx ValueNat = ValueSort typeSort
valueIntroType_ _ctx ValueNatZ = ValueNat
valueIntroType_ _ctx (ValueNatS _) = ValueNat ~> ValueNat

addContext
    :: ValueIntro err s a                  -- ^ x
    -> (a -> Maybe (ValueIntro err s a))   -- ^ context
    -> Var IrrSym a
    -> Maybe (ValueIntro err s (Var b a))
addContext x _ (B _) = Just (F <$> x)
addContext _ f (F x) = fmap F <$> f x
-}
