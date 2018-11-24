{-# LANGUAGE OverloadedStrings #-}
-- | Type-checker.
module Language.PTS.Check (
    type_,
    check_,
    ) where

import Language.PTS.Bound
import Language.PTS.Error
import Language.PTS.Pretty
import Language.PTS.Specification
import Language.PTS.Sym
import Language.PTS.Term
import Language.PTS.Value

#ifdef LANGUAGE_PTS_HAS_NAT
import Language.PTS.Smart
#endif

-------------------------------------------------------------------------------
-- Type-checker
-------------------------------------------------------------------------------

-- | We can infer the type of 'TermInf'...
type_
    :: (Eq a, Show a, PrettyPrec a, Specification s, MonadErr m, PrettyPrec err, AsErr err)
    => (a -> Maybe (ValueIntro err s a))           -- ^ environment
    -> TermInf s a                                 -- ^ term to type-check
    -> m (ValueIntro err s a, ValueIntro err s a)  -- ^ as result we get evaluated term and its type.
type_ = rtype_ []

-- | ... and check the type of 'TermChk'.
check_
    :: (Eq a, Show a, PrettyPrec a, Specification s, MonadErr m, PrettyPrec err, AsErr err)
    => (a -> Maybe (ValueIntro err s a))  -- ^ environment
    -> TermChk s a                        -- ^ term to check
    -> ValueIntro err s a                 -- ^ expected type
    -> m (ValueIntro err s a)             -- ^ as result we get evaluated term
check_ = rcheck_ []

-------------------------------------------------------------------------------
-- Synthesis
-------------------------------------------------------------------------------

rtype_
    :: (Eq a, Show a, PrettyPrec a, Specification s, MonadErr m, PrettyPrec err, AsErr err)
    => [PrettyM Doc] -- ^ terms we walked through, for error reporting
    -> (a -> Maybe (ValueIntro err s a))
    -> TermInf s a
    -> m (ValueIntro err s a, ValueIntro err s a)
rtype_ ts ctx term = case term of
    Var a -> case ctx a of
        Nothing -> throwErr $ VariableNotInScope (ppp0 a) ts
        Just t  -> return (return a, t)
    Sort s -> case axiom s of
        Nothing -> throwErr $ SortWithoutAxiom (ppp0 s) ts
        Just s' -> return $ (ValueSort s, ValueSort s')
    Ann x t -> do
        (t', _) <- rsort_ ts'  ctx t
        x' <- rcheck_ ts' ctx x t'
        return (x', t')
    App f x -> do
        (f', ft) <- rtype_ ts' ctx f
        case ft of
            ValuePi _n a b -> do
                x' <- rcheck_ ts' ctx x a
                return (valueApp f' x', instantiate1 x' b)
            _ -> throwErr $ NotAFunction (ppp0 ft) (ppp0 f) (ppp0 x) ts'
    Pi x a b -> do
        (a', as) <- rsort_ ts' ctx a
        (b', bs) <- rsort_ ts' (addContext a' ctx) (fromScopeH b)
        case rule as bs of
            Nothing -> throwErr $ NoRule (ppp0 as) (ppp0 bs) ts
            Just cs -> return (ValuePi x a' (toScope b'), ValueSort cs)

#ifdef LANGUAGE_PTS_HAS_BOOL
    TermBool   -> return (ValueBool, ValueSort typeSort)
    TermTrue   -> return (ValueTrue, ValueBool)
    TermFalse  -> return (ValueFalse, ValueBool)

    TermBoolElim x p t f b -> do
        -- Check b first, even we have it latter in the rule.
        b' <- rcheck_ ts' ctx b ValueBool

        let as = typeSort -- sort of Booleans

        -- check sorts
        let pp   = fromScopeH p
        (pp', bs) <- rsort_ ts' (addContext ValueBool ctx) pp
        let p' = toScope pp'

        case rule as bs of
            Nothing -> throwErr $ NoRule (ppp0 as) (ppp0 bs) ts
            Just _  -> pure ()

        t' <- rcheck_ ts' ctx t (instantiate1 ValueTrue  p')
        f' <- rcheck_ ts' ctx f (instantiate1 ValueFalse p')

        return (valueBoolElim x p' t' f' b', instantiate1 b' p')

#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM
    TermAnd x y -> do
        x' <- rcheck_ ts' ctx x ValueBool
        y' <- rcheck_ ts' ctx y ValueBool
        return (valueAnd x' y', ValueBool)
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
    TermNat    -> return (ValueNat, ValueSort typeSort)
    TermNatZ   -> return (ValueNatZ, ValueNat)
    TermNatS n -> do
        n' <- rcheck_ ts' ctx n ValueNat
        return (ValueNatS n', ValueNat)

    TermNatElim x p z s n -> do
        -- Check n first, even we have it latter in the rule.
        n' <- rcheck_ ts' ctx n ValueNat

        let as = typeSort -- sort of Natural numbers

        -- check sorts
        let pp   = fromScopeH p
        (pp', bs) <- rsort_ ts' (addContext ValueNat ctx) pp
        let p' = toScope pp'

        case rule as bs of
            Nothing -> throwErr $ NoRule (ppp0 as) (ppp0 bs) ts
            Just _  -> pure ()

        z' <- rcheck_ ts' ctx z $ instantiate1 ValueNatZ p'
        s' <- rcheck_ ts' ctx s $ ValuePi "l" ValueNat $ toScope $
            instantiate1 (pure (B "l")) (fmap F p') ~>
            instantiate1 (ValueNatS (pure (B "l"))) (fmap F p')

        return (valueNatElim x p' z' s' n', instantiate1 n' p')

#ifdef LANGUAGE_PTS_HAS_NAT_PRIM
    TermPlus x y -> do
        x' <- rcheck_ ts' ctx x ValueNat
        y' <- rcheck_ ts' ctx y ValueNat
        return (valuePlus x' y', ValueNat)

    TermTimes x y -> do
        x' <- rcheck_ ts' ctx x ValueNat
        y' <- rcheck_ ts' ctx y ValueNat
        return (valueTimes x' y', ValueNat)
#endif
#endif
  where
    ts' :: [PrettyM Doc]
    ts' = ppp0 term : ts

-------------------------------------------------------------------------------
-- Infer sort
-------------------------------------------------------------------------------

-- | Check that term is a of right sort type.
--
-- More special version of 'rcheck_'.
rsort_
    :: (Eq a, Show a, PrettyPrec a, Specification s, MonadErr m, PrettyPrec err, AsErr err)
    => [PrettyM Doc]
    -> (a -> Maybe (ValueIntro err s a))
    -> TermInf s a
    -> m (ValueIntro err s a, s)
rsort_ ts ctx term = do
    (x, t) <- rtype_ ts ctx term
    case t of
        ValueSort s -> return (x, s)
        _           -> throwErr $ SomeErr "not a sort"

-------------------------------------------------------------------------------
-- Checking
-------------------------------------------------------------------------------

rcheck_
    :: (Eq a, Show a, PrettyPrec a, Specification s, MonadErr m, PrettyPrec err, AsErr err)
    => [PrettyM Doc] -- ^ terms we walked through, for error reporting
    -> (a -> Maybe (ValueIntro err s a))
    -> TermChk s a
    -> ValueIntro err s a
    -> m (ValueIntro err s a)
rcheck_ ts ctx term t = case term of
    Inf u -> do
        (u', t') <- rtype_ ts' ctx u
        if t == t'
        then return u'
        else throwErr $ TypeMismatch (ppp0 t) (ppp0 t') (ppp0 u) ts

    Lam x e -> case t of
        ValuePi _ a b -> do
            let ee = fromScopeH e
            let bb = fromScope b
            bb' <- rcheck_ ts' (addContext a ctx) ee bb
            return (ValueLam x a (toScope bb'))
        _ -> throwErr $ LambdaNotPi (ppp0 t) (ppp0 term) ts
  where
    ts' :: [PrettyM Doc]
    ts' = ppp0 term : ts

addContext
    :: ValueIntro err s a                  -- ^ x
    -> (a -> Maybe (ValueIntro err s a))   -- ^ context
    -> Var IrrSym a
    -> Maybe (ValueIntro err s (Var b a))
addContext x _ (B _) = Just (F <$> x)
addContext _ f (F x) = fmap F <$> f x
