-- | Demonstration of error reporting.
module Language.PTS.Examples.Errors (
    scopeError,
    annotationError,
    evaluatorError,
    ) where

-------------------------------------------------------------------------------
-- Error cases
-------------------------------------------------------------------------------

-- |
--
-- >>> demo_ basicCtx ("Boo" :: Term LambdaStar)
-- error:
-- • Variable not in scope Boo
scopeError :: ()
scopeError = ()

-- |
--
-- >>> demo_ basicCtx (lam_ "x" "x" -:- "Bool" :: Term STLC)
-- error:
-- • The lambda expression λ x → x doesn't have a Pi-type
-- • Annotated with Bool
-- • when checking expression
--   λ x → x : Bool
--
annotationError :: ()
annotationError = ()

-- |
--
-- >>> demo_ basicCtx ("True" @@ "False" :: Term LambdaStar)
-- error:
-- • Couldn't match actual type Bool with a function type
-- • In the application of True
-- • to the value False
-- • when checking expression
--   True False
--
-- If we try to apply variable to variable values, it's ok however.
-- We can be weird, so @"True"@ is actually a function:
--
-- >>> prettyPut ("True" @@ "False" :: Value LambdaStar)
-- True False
--
-- Yet, if we apply to a sort, or Pi-type or something else obviously incorrect:
-- value will fail:
--
-- >>> prettyPut (sort_ LambdaStar `valueApp` "False" :: Value LambdaStar)
-- panic 'apply': Trying to apply not-a-lambda ⋆
--
-- We don't print a value we try to apply, because it's still not evaluated.
-- (often some variable in a scope).
--
evaluatorError :: ()
evaluatorError =  ()

-- $setup
-- >>> :set -XOverloadedStrings -XTypeApplications
-- >>> import Language.PTS
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Systems
-- >>> import Language.PTS.Examples.Contexts
