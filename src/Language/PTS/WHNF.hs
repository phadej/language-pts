module Language.PTS.WHNF (WHNF (..)) where

import Language.PTS.Bound
import Language.PTS.Term
import Language.PTS.Smart

-- | Weak-head normal form.
--
-- >>> prettyPut $ whnf (lambdaStarIdentity @@ "Bool" @@ "True" :: Term LambdaStar)
-- True
--
-- Note: the evaluation proceeds even for ill-typed terms:
--
-- >>> prettyPut $ whnf (lambdaStarIdentity @@ "Int" @@ "True" :: Term LambdaStar)
-- True
--
-- /TODO:/ @nat@ flag
class WHNF t where
    whnf :: t s a -> t s a

instance WHNF TermInf where
    whnf (Ann x t) = ann_ (whnf x) (whnf t) -- here's the choice, to whnf type in ann or not.
    whnf (App f a) = case whnf f of
        Ann (Lam _ b) t@(Pi _ at _) ->
            ann_ (whnf $ instantiate1H (ann_ a at) b) t
        f'    -> App f' a
    whnf e = e

instance WHNF TermChk where
    whnf (Inf u)  = Inf (whnf u)
    whnf e@Lam {} = e

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> import Language.PTS
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Systems
-- >>> import Language.PTS.Examples (lambdaStarIdentity)
