{-# LANGUAGE OverloadedStrings #-}
-- | Evaluation.
--
-- Performs β-reductions.
--
-- Note to self, various reductions (in Coq):
--
-- * /beta-reduction/
--   \( (\lambda x. b)\, a \leadsto_\beta b [x \mapsto a] \).
--
-- * /delta-reduction/, for unfolding definitions
--   \( D \leadsto_\delta e\),
--   if \(D = M\) is defined.
--
-- * /iota-reduction/, for primitive recusion rules, general recursion (@fix@)
--   and case analysis.
--
-- * /zeta-reduction/, for local definitions
--   \( \mathsf{let}\,x = a\,\mathsf{in}\,b \leadsto_\zeta b [x \mapsto a] \).
--
-- There's also
--
-- * /eta-conversion/
--   \(\lambda x. e\, x \leadsto_\eta e\),
--   if \(x\) is free in \(e\).
--   /Note:/ The \((\lambda x. f\, x)\,y\) reduces to \(f\,y\) via both, beta and eta, reductions.
--
module Language.PTS.Eval (
    eval_,
    -- $eta
    ) where

#ifdef LANGUAGE_PTS_HAS_NAT
import Language.PTS.Smart
#endif

import Control.Lens (review)

import Language.PTS.Bound
import Language.PTS.Error
import Language.PTS.Pretty
import Language.PTS.Specification
import Language.PTS.Sym
import Language.PTS.Term
import Language.PTS.Value
import Language.PTS.Value.Check

-- | Evaluate 'Term' into 'Value'.
class Eval t where
    eval_
        :: (Specification s, PrettyPrec err, AsErr err, PrettyPrec a)
        => (a -> Maybe (ValueIntro err s a))  -- ^ Context
        -> t s a                              -- ^ Term
        -> ValueIntro err s a                 -- ^ Term's type
        -> ValueIntro err s a                 -- ^ Evaluated term, value

instance Eval TermInf where eval_ ctx term _ = evalInf ctx term
instance Eval TermChk where eval_ = evalChk

evalInf
    :: (Specification s, PrettyPrec err, AsErr err, PrettyPrec a)
    => (a -> Maybe (ValueIntro err s a))  -- ^ Context
    -> TermInf s a
    -> ValueIntro err s a
evalInf _ctx (Var x)         = ValueCoerce (ValueVar x)
evalInf _ctx (Sort s)        = ValueSort s
evalInf  ctx (Ann x t)       = evalChk ctx x (evalInf ctx t)
evalInf  ctx (Pi n a b)      = ValuePi n a' (toScope $ evalInf (addContext a' ctx) $ fromScopeH b)
  where
    a' = evalInf ctx a

-- Application is tricky
evalInf  ctx (App f (Inf x)) = valueApp (evalInf ctx f) (evalInf ctx x)
evalInf  ctx (App f x)       = case evalInf ctx f of
    ValueLam _n t f' -> instantiate1 (evalChk ctx x t) f'
    ValueErr err     -> ValueErr err
    ValueCoerce f'   -> case valueType_ ctx f' of
        ValueErr err    -> ValueErr err
        ValuePi _x t _b -> ValueCoerce (ValueApp f' (evalChk ctx x t))
        t'              -> ValueErr $ review _Err $ ApplyPanic "not-pi" $ ppp0 (t', x)
    f'               -> ValueErr $ review _Err $ ApplyPanic "eval-inf" (ppp0 f')

#ifdef LANGUAGE_PTS_HAS_BOOL
evalInf _ctx TermBool                 = ValueBool
evalInf _ctx TermTrue                 = ValueTrue
evalInf _ctx TermFalse                = ValueFalse
evalInf  ctx (TermBoolElim x p t f b) = valueBoolElim x
    p' t' f' b'
  where
    p' = Scope $ evalInf (addContext ValueBool ctx) $ fromScopeH p
    t' = evalChk ctx t $ instantiate1 ValueTrue p'
    f' = evalChk ctx f $ instantiate1 ValueFalse p'
    b' = evalChk ctx b ValueBool

#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM
evalInf  ctx (TermAnd x y) = valueAnd
    (evalChk ctx x ValueBool)
    (evalChk ctx y ValueBool)
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
evalInf _ctx TermNat                = ValueNat
evalInf _ctx TermNatZ               = ValueNatZ
evalInf  ctx (TermNatS n)           = ValueNatS (evalChk ctx n ValueNat)
evalInf  ctx (TermNatElim x p z s n) = valueNatElim x
    p' z' s' n'
  where
    p' = Scope $ evalInf (addContext ValueNat ctx) $ fromScopeH p
    z' = evalChk ctx z $ instantiate1 ValueNatZ p'
    s' = evalChk ctx s $ ValuePi "l" ValueNat $ toScope $
        instantiate1 (pure (B "l")) (fmap F p') ~>
        instantiate1 (ValueNatS (pure (B "l"))) (fmap F p')
    n' = evalChk ctx n ValueNat

#ifdef LANGUAGE_PTS_HAS_NAT_PRIM
evalInf ctx (TermPlus x y) = valuePlus
    (evalChk ctx x ValueNat)
    (evalChk ctx y ValueNat)

evalInf ctx (TermTimes x y) = valueTimes
    (evalChk ctx x ValueNat)
    (evalChk ctx y ValueNat)
#endif
#endif

evalChk
    :: (Specification s, PrettyPrec err, AsErr err, PrettyPrec a)
    => (a -> Maybe (ValueIntro err s a))  -- ^ Context
    -> TermChk s a
    -> ValueIntro err s a
    -> ValueIntro err s a
evalChk  ctx (Inf u)        _t               = evalInf ctx u
evalChk  ctx (Lam n b)      (ValuePi _ t tb) = eta' n t $ evalChk (addContext t ctx) (fromScopeH b) (fromScope tb)
evalChk _ctx term@(Lam _ _) t                = ValueErr $ review _Err $ LambdaNotPi (ppp0 t) (ppp0 term) []

addContext
    :: ValueIntro err s a                  -- ^ x
    -> (a -> Maybe (ValueIntro err s a))   -- ^ context
    -> Var IrrSym a
    -> Maybe (ValueIntro err s (Var b a))
addContext x _ (B _) = Just (F <$> x)
addContext _ f (F x) = fmap F <$> f x

-- | Construct lambda from a bound scope.
--
-- If @eta@ flag is enabled, perform eta-conversion.
eta'
    :: IrrSym                           -- ^ variable
    -> ValueIntro err s a               -- ^ variable's type
    -> ValueIntro err s (Var IrrSym a)  -- ^ body
    -> ValueIntro err s a               -- ^ lambda
#ifdef LANGUAGE_PTS_HAS_ETA
eta' _ t (ValueCoerce (ValueApp f (ValueCoerce (ValueVar (B _)))))
    -- bound variable is free in @f@
    | Just f' <- traverse (unvar (const Nothing) Just) f = ValueCoerce f'
#endif
eta' n t s = ValueLam n t (toScope s)

#if LANGUAGE_PTS_HAS_ETA
-- $eta
--
-- As @eta@ flag is __on__, eta-conversion is performed as well.
--
-- >>> let term = lam_ "x" $ "f" @@ "x" :: TermChk LambdaStar Sym
-- >>> prettyPut term
-- λ x → f x
--
-- >>> let ctx = const $ Just $ "a" ~> "b"
-- >>> prettyPut (evalChk ctx term ("a" ~> "b") :: Value LambdaStar)
-- f
--
#else
-- $eta
--
-- As @eta@ flag is __off__, eta-conversion __is not__ performed.
--
-- >>> let term = lam_ "x" $ "f" @@ "x" :: TermChk LambdaStar Sym
-- >>> prettyPut term
-- λ x → f x
--
-- >>> let ctx = const $ Just $ "a" ~> "b"
-- >>> prettyPut (evalChk ctx term ("a" ~> "b") :: Value LambdaStar)
-- λ (x : a) → f x
--
#endif

-- $setup
-- >>> import Language.PTS.Systems
-- >>> import Language.PTS.Smart
-- >>> let pp  = prettyPut :: TermInf LambdaStar Sym -> IO ()
-- >>> let pp' = prettyPut :: Value LambdaStar -> IO ()
