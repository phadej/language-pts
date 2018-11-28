{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
#ifdef LANGUAGE_PTS_HAS_EQUALITY
#ifdef LANGUAGE_PTS_HAS_BOOL
#ifdef LANGUAGE_PTS_HAS_NAT
#ifdef LANGUAGE_PTS_HAS_SIGMA
#define EQUALITY_EXAMPLES
#endif
#endif
#endif
#endif
module Language.PTS.Examples.Equality (
#ifdef EQUALITY_EXAMPLES
    equalityScript,
#endif
    ) where

#ifdef EQUALITY_EXAMPLES
import Language.PTS
import Language.PTS.Bound

-- |
--
-- >>> runLoud $ spec_ (MartinLof 0) >> equalityScript
-- -- 1. Non-dependent elimination: if
-- -----------------------------------
-- --
-- λ» :define if : ∀ r → 𝔹 → r → r → r
--               = λ r b t f → 𝔹-elim (λ _ → r) t f b
-- --
-- -- 2. Negation, not
-- -------------------
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
-- -- 3. Simple equality examples
-- ------------------------------
-- --
-- λ» :example refl : Eq 𝔹 (not true) false
-- ↪ refl : Eq 𝔹 false false
-- --
-- λ» :example refl : Eq 𝔹 (not false) true
-- ↪ refl : Eq 𝔹 true true
-- --
-- -- 4. Lemma: Not is involutive
-- ------------------------------
-- --
-- λ» :define not-inv
-- : ∏ (b : 𝔹) → Eq 𝔹 b (not (not b))
-- = λ b → 𝔹-elim (λ x → Eq 𝔹 x (not (not x))) refl refl b
-- --
-- -- 5. Example with exists
-- -------------------------
-- --
-- λ» :define not-surj
-- : ∏ (x : 𝔹) → ∑ (y : 𝔹) → Eq 𝔹 x (not y)
-- = λ x → 𝔹-elim (λ b → ∑ (y : 𝔹) → Eq 𝔹 b (not y))
--                (pair false refl)
--                (pair true refl)
--                x
-- ∎
--
equalityScript :: forall s m. Script s m => m ()
equalityScript = do
    section_ "Non-dependent elimination: if"

    define_ "if"
        $$ forall_ "r" (TermBool ~> "r" ~> "r" ~> "r")
        $$ lams_ ["r", "b", "t", "f"]
              (Inf $ TermBoolElim "_" (liftH "r") "t" "f" "b")

    section_ "Negation, not"

    define_ "not"
        $$ TermBool ~> TermBool
        $$ lam_ "b" ("if" @@@ TermBool @@ "b" @@@ TermFalse @@@ TermTrue)

    example_ "not"
    example_ $ "not" @@@ TermTrue
    example_ $ "not" @@@ TermFalse

    section_ "Simple equality examples"

    example_ $$ Refl -:-
        Equality TermBool ("not" @@@ TermTrue) (Inf TermFalse)

    example_ $$ Refl -:-
        Equality TermBool ("not" @@@ TermFalse) (Inf TermTrue)

    section_ "Lemma: Not is involutive"

    let ty b = Equality TermBool b ("not" @@ ("not" @@ b))
    define_ "not-inv"
        $$ pi_ "b" TermBool (ty "b")
        $$ lam_ "b" (Inf $ TermBoolElim "x" (abstract1HSym "x" $ ty "x") Refl Refl "b")

    section_ "Example with exists"

    let ty2 :: TermInf s Sym -> TermInf s Sym
        ty2 x = sigma_ "y" TermBool (Equality TermBool (Inf x) ("not" @@ "y"))
    define_ "not-surj"
        $$ pi_ "x" TermBool (ty2 "x")
        $$ lam_ "x" (Inf $ TermBoolElim "b" (abstract1HSym "b" $ ty2 "b")
            (Pair (Inf TermFalse) Refl)
            (Pair (Inf TermTrue) Refl)
            "x")

#endif

-- $setup
-- >>> :seti -XOverloadedStrings -XTypeApplications
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Systems
