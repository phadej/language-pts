module Language.PTS.Value.Check (
    valueType_
    ) where

import Control.Lens ((#))

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
    Nothing -> ValueErr $ _Err # VariableNotInScope (ppp0 a) []
    Just t  -> t
valueType_ ctx (ValueApp f x) = case valueType_ ctx f of
    ValuePi _n _a b -> instantiate1 x b
    ValueErr err    -> ValueErr err
    ft              -> ValueErr $ _Err # NotAFunction (ppp0 ft) (ppp0 f) (ppp0 x) []

#ifdef LANGUAGE_PTS_HAS_BOOL
valueType_ _ctx (ValueBoolElim _ p _ _ b) = instantiate1 (ValueCoerce b) p
#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM
valueType_ _ctx (ValueAnd _ _) = ValueBool
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
valueType_ _ctx (ValueNatElim _ p _ _ n) = instantiate1 (ValueCoerce n) p

#ifdef LANGUAGE_PTS_HAS_NAT_PRIM
valueType_ _ctx (ValuePlus _ _) = ValueNat
#endif
#endif
