{-# LANGUAGE OverloadedStrings #-}
-- | Type-checker.
module Language.PTS.Check (
    type_,
    check_,
    ) where

import Control.Monad (unless)

import Language.PTS.Bound
import Language.PTS.Error
import Language.PTS.Eval
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
    => (a -> Maybe (ValueIntro err s a))  -- ^ environment
    -> TermInf s a                        -- ^ term to type-check
    -> m (ValueIntro err s a)             -- ^ as result we get term's type.
type_ = rtype_ []

-- | ... and check the type of 'TermChk'.
check_
    :: (Eq a, Show a, PrettyPrec a, Specification s, MonadErr m, PrettyPrec err, AsErr err)
    => (a -> Maybe (ValueIntro err s a))  -- ^ environment
    -> TermChk s a                        -- ^ term to check
    -> ValueIntro err s a                 -- ^ expected type
    -> m ()
check_ = rcheck_ []

-------------------------------------------------------------------------------
-- Synthesis
-------------------------------------------------------------------------------

rtype_
    :: (Eq a, Show a, PrettyPrec a, Specification s, MonadErr m, PrettyPrec err, AsErr err)
    => [PrettyM Doc] -- ^ terms we walked through, for error reporting
    -> (a -> Maybe (ValueIntro err s a))
    -> TermInf s a
    -> m (ValueIntro err s a)
rtype_ ts ctx term = case term of
    Var a -> case ctx a of
        Nothing -> throwErr $ VariableNotInScope (ppp0 a) ts
        Just t  -> return t
    Sort s -> case axiom s of
        Nothing -> throwErr $ SortWithoutAxiom (ppp0 s) ts
        Just s' -> return $ ValueSort s'
    Ann x t -> do
        s <- rsort_ ts'  ctx t
        let t' = eval_ ctx t (ValueSort s)
        rcheck_ ts' ctx x t'
        return t'
    App f x -> do
        ft <- rtype_ ts' ctx f
        case ft of
            ValuePi _n a b -> do
                rcheck_ ts' ctx x a
                return $ instantiate1 (eval_ ctx x a) b
            _ -> throwErr $ NotAFunction (ppp0 ft) (ppp0 f) (ppp0 x) ts'
    Pi _n a b -> do
        as <- rsort_ ts' ctx a
        bs <- rsort_ ts' (addContext (eval_ ctx a (ValueSort as)) ctx) (fromScopeH b)
        case rule as bs of
            Nothing -> throwErr $ NoRule (ppp0 as) (ppp0 bs) ts
            Just cs -> return $ ValueSort cs

#ifdef LANGUAGE_PTS_HAS_BOOL
    TermBool   -> return (ValueSort typeSort)
    TermTrue   -> return ValueBool
    TermFalse  -> return ValueBool

    TermBoolElim _x p t f b -> do
        -- Check b first, even we have it latter in the rule.
        rcheck_ ts' ctx b ValueBool

        let as = typeSort -- sort of Booleans

        -- check sorts
        let p'   = fromScopeH p
        let ctx' = addContext ValueBool ctx
        bs <- rsort_ ts' (addContext ValueBool ctx) p'

        case rule as bs of
            Nothing -> throwErr $ NoRule (ppp0 as) (ppp0 bs) ts
            Just _  -> pure ()

        let p'' = toScope $ eval_ ctx' p' (ValueSort bs)

        rcheck_ ts' ctx t (instantiate1 ValueTrue  p'')
        rcheck_ ts' ctx f (instantiate1 ValueFalse p'')

        return $ instantiate1 (eval_ ctx b ValueBool) p''

#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM
    TermAnd x y -> do
        rcheck_ ts' ctx x ValueBool
        rcheck_ ts' ctx y ValueBool
        return ValueBool
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
    TermNat    -> return (ValueSort typeSort)
    TermNatZ   -> return ValueNat
    TermNatS n -> do
        rcheck_ ts' ctx n ValueNat
        return ValueNat

    TermNatElim _x p z s n -> do
        -- Check n first, even we have it latter in the rule.
        rcheck_ ts' ctx n ValueNat

        let as = typeSort -- sort of Natural numbers
    
        -- check sorts
        let p'   = fromScopeH p
        let ctx' = addContext ValueNat ctx
        bs <- rsort_ ts' (addContext ValueNat ctx) p'

        case rule as bs of
            Nothing -> throwErr $ NoRule (ppp0 as) (ppp0 bs) ts
            Just _  -> pure ()


        let p'' = toScope $ eval_ ctx' p' (ValueSort bs)

        rcheck_ ts' ctx z $ instantiate1 ValueNatZ p''
        rcheck_ ts' ctx s $ ValuePi "l" ValueNat $ toScope $
            instantiate1 (pure (B "l")) (fmap F p'') ~>
            instantiate1 (ValueNatS (pure (B "l"))) (fmap F p'')

        return $ instantiate1 (eval_ ctx n ValueNat) p''

#ifdef LANGUAGE_PTS_HAS_NAT_PRIM
    TermPlus x y -> do
        rcheck_ ts' ctx x ValueNat
        rcheck_ ts' ctx y ValueNat
        return ValueNat
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
    -> m s
rsort_ ts ctx term = do
    t <- rtype_ ts ctx term
    case t of
        ValueSort s' -> return s'
        _            -> throwErr $ SomeErr "not a sort"

-------------------------------------------------------------------------------
-- Checking
-------------------------------------------------------------------------------

{-
-- | Check that term is a of right sort type.
--
-- More special version of 'rcheck_'.
rcheckSort_
    :: (Eq a, Show a, PrettyPrec a, Specification s, MonadErr m, PrettyPrec err, AsErr err)
    => [PrettyM Doc]
    -> (a -> Maybe (ValueIntro err s a))
    -> TermChk s a
    -> s
    -> m ()
rcheckSort_ ts ctx term s = case term of
    Inf u -> do
        t' <- rtype_ ts' ctx u
        case t' of
            ValueSort s' -> unless (s == s') $ throwErr $ SortMismatch (ppp0 s) (ppp0 s') (ppp0 u) ts
            _            -> throwErr $ SomeErr "not a sort"
    Lam _ _ -> throwErr $ SomeErr "Lambda cannot have sort type"
  where
    ts' :: [PrettyM Doc]
    ts' = ppp0 term : ts
-}

rcheck_
    :: (Eq a, Show a, PrettyPrec a, Specification s, MonadErr m, PrettyPrec err, AsErr err)
    => [PrettyM Doc] -- ^ terms we walked through, for error reporting
    -> (a -> Maybe (ValueIntro err s a))
    -> TermChk s a
    -> ValueIntro err s a
    -> m ()
rcheck_ ts ctx term t = case term of
    Inf u -> do
        t' <- rtype_ ts' ctx u
        unless (t == t') $ throwErr $ TypeMismatch (ppp0 t) (ppp0 t') (ppp0 u) ts

    Lam _n e -> case t of
        ValuePi _ a b -> do
            let e' = fromScopeH e
            let b' = fromScope b
            rcheck_ ts' (addContext a ctx) e' b'
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
