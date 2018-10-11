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
    Eval (..),
    -- $eta
    ) where

import Language.PTS.Bound
import Language.PTS.Error
import Language.PTS.Pretty
import Language.PTS.Smart
import Language.PTS.Specification
import Language.PTS.Sym
import Language.PTS.Term
import Language.PTS.Value
import Language.PTS.WHNF

-- | Evaluate 'Term' into 'Value'.
class Eval t where
    eval_ :: (PrettyPrec err, AsErr err, Specification s) => t s a -> ValueIntro err s a

instance Eval TermInf where
    eval_ (Var x)          = ValueCoerce (ValueVar x)
    eval_ (Sort s)         = ValueSort s
    eval_ (App f x)        = case whnf f of
        -- do reduction in Term, as far as possible. Then convert to 'Value'.
        Ann (Lam _ b) (Pi _ xt _) ->
            eval_ (instantiate1H (ann_ x xt) b)
        _ -> valueApp (eval_ f) (eval_ x)
    eval_ (Ann x _  )      = eval_ x
    eval_ (Pi n a b)       = ValuePi n (eval_ a)  (toScope $ eval_ $ fromScopeH b)

#ifdef LANGUAGE_PTS_HAS_NAT
    eval_ TermNat               = ValueNat
    eval_ TermNatZ              = ValueNatZ
    eval_ (TermNatS n)          = ValueNatS (eval_ n)
    eval_ (TermNatElim a z s n) = valueNatElim (eval_ a) (eval_ z) (eval_ s) (eval_ n)
#endif

instance Eval TermChk where
    eval_ (Inf u)   = eval_ u
    eval_ (Lam n b) = eta' n $ eval_ $ fromScopeH b

-- | Construct lambda from a bound scope.
--
-- If @eta@ flag is enabled, perform eta-conversion.
eta' :: IrrSym -> ValueIntro err s (Var IrrSym a) -> ValueIntro err s a
#ifdef LANGUAGE_PTS_HAS_ETA
eta' _ (ValueCoerce (ValueApp f (ValueCoerce (ValueVar (B _)))))
    -- bound variable is free in @f@
    | Just f' <- traverse (unvar (const Nothing) Just) f = ValueCoerce f'
#endif
eta' n s = ValueLam n (toScope s)

#if LANGUAGE_PTS_HAS_ETA
-- $eta
--
-- As @eta@ flag is __on__, eta-conversion is performed as well.
--
-- >>> let term = lam_ "x" $ "f" @@ "x" :: TermChk LambdaStar Sym
-- >>> prettyPut term
-- λ x → f x
--
-- >>> prettyPut (eval_ term :: Value LambdaStar)
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
-- >>> prettyPut (eval_ term :: Value LambdaStar)
-- λ x → f x
--
#endif

-- $setup
-- >>> import Language.PTS.Systems
-- >>> let pp  = prettyPut :: TermInf LambdaStar Sym -> IO ()
-- >>> let pp' = prettyPut :: Value LambdaStar -> IO ()
