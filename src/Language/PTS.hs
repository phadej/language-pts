{-# LANGUAGE ScopedTypeVariables #-}
-- |
--
-- === Comments
--
-- * LambdaPi paper doesn't tell why values are divided into neutral terms
--   and a lambda abstraction. Frank Pfenning's lecture notes give another
--   explation. Values (neutral terms) (@'Value' ~ 'ValueIntro'@) are introduced,
--   or they meet with elimination forms ('ValueElim') which are extracted from
--   a hypothesis.
--   <https://www.cs.cmu.edu/~fp/courses/atp/handouts/ch3-seqcalc.pdf>
-- * In LambdaPi paper only \(Term\uparrow\) (inferred) are substituted.
--   Therefore we have @'Scope' 'TermInf'@. However binding forms close over
--   \(Term\downarrow\), we wrap them in 'TermChkT', and use "Bound.ScopeT" to
--   make all that look simple. Noteworthy is the fact, that 'TermChk' is not a
--   'Monad', but 'TermChkT' is a 'Bound'.
-- * "Language.PTS.Smart" defines small DSL to write terms in Haskell
--   (Haskell as a meta-language!). We rely on @FunctionalDependencies@
--   to make combinators work for 'Term' and 'Value'.
--   Similar idea is used in the @lucid_@ package.
--
module Language.PTS (
    -- * Terms and values (and symbols and errors)
    module Language.PTS.Term,
    module Language.PTS.Value,
    module Language.PTS.Sym,
    module Language.PTS.Error,
    -- * type-check, eval, quote
    module Language.PTS.Check,
    module Language.PTS.Eval,
    module Language.PTS.Quote,
    -- * PTS specification
    module Language.PTS.Specification,
    -- * DSL for terms and values
    module Language.PTS.Smart,
    module Language.PTS.Script,
    -- * WHNF is an example "evaluator"
    module Language.PTS.WHNF,
    -- * Other
    demo_,
  ) where

import Language.PTS.Check
import Language.PTS.Error
import Language.PTS.Eval
import Language.PTS.Pretty
import Language.PTS.Quote
import Language.PTS.Script
import Language.PTS.Smart
import Language.PTS.Specification
import Language.PTS.Sym
import Language.PTS.Term
import Language.PTS.Value
import Language.PTS.WHNF

import qualified Text.PrettyPrint.Compact as PP

-- | Pretty-print the term, its normal form and type.
--
-- >>> demo_ basicCtx $ systemfIdentity @@ "Bool" @@ "True"
-- (λ a x → x : ∀ a → a → a) Bool True ↪ True : Bool
demo_ :: forall s. Specification s => (Sym -> Maybe (Value s)) -> Term s -> IO ()
demo_ ctx term = case type_ ctx term >>= errorlessValueIntro of
    Left err -> prettyPut (err :: Err)
    Right (t :: Value s) -> case errorlessValueIntro $ eval_ ctx term t of
        Left err -> prettyPut (err :: Err)
        -- we quote term before printing (strips type lambda type annotations)
        Right v  -> prettyPutWith opts $ pppHang 4
            (ppp0 term)
            (pppChar '↪' <+> ppp0 (quote_ v) </> pppChar ':' <+> ppp0 t)

  where
    opts = PP.defaultOptions { PP.optsPageWidth = 60 }

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> import Language.PTS.Examples
