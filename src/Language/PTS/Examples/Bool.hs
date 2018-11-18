{-# LANGUAGE OverloadedStrings #-}
module Language.PTS.Examples.Bool (
#if defined(LANGUAGE_PTS_HAS_BOOL) && defined(LANGUAGE_PTS_HAS_NAT)
    boolScript,
#endif
    ) where

#if defined(LANGUAGE_PTS_HAS_BOOL) && defined(LANGUAGE_PTS_HAS_NAT)
import Language.PTS

-- | Examples of built-in Booleans.
-- We need dependent types to be able to use dependent @𝔹-elim@.
--
-- >>> runLoud $ spec_ (MartinLof 0) >> boolScript
-- -- 1. Constants
-- ---------------
-- --
-- λ» :example 𝔹
-- ↪ 𝔹 : 𝓤
-- --
-- λ» :example true
-- ↪ true : 𝔹
-- --
-- λ» :example false
-- ↪ false : 𝔹
-- --
-- -- 2. Non-dependent elimination: if
-- -----------------------------------
-- --
-- λ» :define if : ∀ r → 𝔹 → r → r → r
--               = λ a b t f → 𝔹-elim (λ _ → a : 𝔹 → 𝓤) t f b
-- --
-- -- 3. Some simple functions on Booleans
-- ---------------------------------------
-- --
-- -- 3.1. Negation, not
-- --
-- λ» :define not : 𝔹 → 𝔹 = λ b → if 𝔹 b false true
-- --
-- λ» :example not
-- ↪ λ b → 𝔹-elim (λ _ → 𝔹) false true b : 𝔹 → 𝔹
-- --
-- λ» :example not true
-- ↪ false : 𝔹
-- --
-- λ» :example not false
-- ↪ true : 𝔹
-- --
-- -- 3.2. Conjunction, and
-- --
-- λ» :define and : 𝔹 → 𝔹 → 𝔹 = λ x y → if 𝔹 x y false
-- --
-- λ» :example and
-- ↪ λ x y → 𝔹-elim (λ _ → 𝔹) y false x : 𝔹 → 𝔹 → 𝔹
-- --
-- λ» :example and true true
-- ↪ true : 𝔹
-- --
-- λ» :example and true false
-- ↪ false : 𝔹
-- --
-- λ» :example and false true
-- ↪ false : 𝔹
-- --
-- λ» :example and false false
-- ↪ false : 𝔹
-- --
-- -- 4. Using dependent elimination
-- ---------------------------------
-- --
-- λ» :define contrived
-- : Π (b : 𝔹) → 𝔹-elim (λ _ → 𝓤 : 𝔹 → 𝓤1) 𝔹 ℕ b
-- = λ b → 𝔹-elim (λ b1 → 𝔹-elim (λ _ → 𝓤 : 𝔹 → 𝓤1) 𝔹 ℕ b1
--                     : 𝔹 → 𝓤)
--                true
--                0
--                b
-- --
-- λ» :example contrived
-- ↪ λ b → 𝔹-elim (λ b → 𝔹-elim (λ _ → 𝓤) 𝔹 ℕ b) true 0 b
-- : Π (b : 𝔹) → 𝔹-elim (λ _ → 𝓤) 𝔹 ℕ b
-- --
-- λ» :example contrived true
-- ↪ true : 𝔹
-- --
-- λ» :example contrived false
-- ↪ 0 : ℕ
-- ∎
--
boolScript :: Script s m => m ()
boolScript = do
    section_ "Constants"

    example_ TermBool
    example_ TermTrue
    example_ TermFalse

    section_ "Non-dependent elimination: if"

    define_ "if"
        $$ forall_ "r" (TermBool ~> "r" ~> "r" ~> "r")
        $$ lams_ ["a", "b", "t", "f"]
              (Inf $ TermBoolElim (lam_ "_" "a" -:- TermBool ~> sort_ typeSort) "t" "f" "b")

    section_ "Some simple functions on Booleans"
    subsection_ "Negation, not"

    define_ "not"
        $$ TermBool ~> TermBool
        $$ lam_ "b" ("if" @@@ TermBool @@ "b" @@@ TermFalse @@@ TermTrue)

    example_ "not"
    example_ $ "not" @@@ TermTrue
    example_ $ "not" @@@ TermFalse

    subsection_ "Conjunction, and"

    define_ "and"
        $$ TermBool ~> TermBool ~> TermBool
        $$ lams_ ["x", "y"] ("if" @@@ TermBool @@ "x" @@ "y" @@@ TermFalse)

    example_ "and"
    example_ $ "and" @@@ TermTrue  @@@ TermTrue
    example_ $ "and" @@@ TermTrue  @@@ TermFalse
    example_ $ "and" @@@ TermFalse @@@ TermTrue
    example_ $ "and" @@@ TermFalse @@@ TermFalse

    -- TODO: change to truth
    section_ "Using dependent elimination"

    let ty = TermBoolElim (lam_ "_" (sort_ typeSort) -:- TermBool ~> sort_ typeSortSort) (Inf TermBool) (Inf TermNat) "b"
    define_ "contrived"
        $$ pi_ "b" TermBool
              (TermBoolElim (lam_ "_" (sort_ typeSort) -:- TermBool ~> sort_ typeSortSort) (Inf TermBool) (Inf TermNat) "b")
        $$ lam_ "b"
            (Inf $ TermBoolElim (lam_ "b" (Inf ty) -:- TermBool ~> sort_ typeSort) (Inf TermTrue) (Inf TermNatZ)  "b")

    example_ "contrived"
    example_ $ "contrived" @@@ TermTrue
    example_ $ "contrived" @@@ TermFalse

-- $setup
-- >>> :set -XOverloadedStrings -XTypeApplications
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Systems
#endif
