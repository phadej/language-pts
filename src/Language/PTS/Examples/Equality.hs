{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
#ifdef LANGUAGE_PTS_HAS_EQUALITY
#ifdef LANGUAGE_PTS_HAS_BOOL
#ifdef LANGUAGE_PTS_HAS_NAT
#ifdef LANGUAGE_PTS_HAS_SIGMA
#ifdef LANGUAGE_PTS_HAS_PROP
#define EQUALITY_EXAMPLES
#endif
#endif
#endif
#endif
#endif
module Language.PTS.Examples.Equality (
#ifdef EQUALITY_EXAMPLES
    equalityScript,
    equivalenceScript,
    leibnizScript,
    inequalityScript,
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


-- | [OPLSS 2014 Type Theory](https://youtu.be/Wpls061J5D0?t=14340)
--
-- >>> runLoud $ spec_ (MartinLof 0) >> equivalenceScript
-- -- 1. Symmetry
-- --------------
-- --
-- λ» :define SYM
-- : 𝓤 → 𝓤 = λ A → ∏ (x : A) → ∏ (y : A) → Eq A x y → Eq A y x
-- λ» :define sym
-- : ∀ A → SYM A
-- = λ A x y p → J A (λ u v w → Eq A v u) (λ q → refl) x y p
-- --
-- -- 1.1. Example
-- --
-- λ» :define nat-fold
-- : ∀ r → ℕ → (r → r) → r → r
-- = λ r n s z → ℕ-elim (λ _ → r) z (λ l → s) n
-- λ» :define succ : ℕ → ℕ = λ n → S n
-- λ» :define plus : ℕ → ℕ → ℕ = λ x y → nat-fold ℕ x succ y
-- --
-- λ» :example refl : Eq ℕ (plus 3 1) (plus 1 3)
-- ↪ refl : Eq ℕ 4 4
-- --
-- λ» :example sym ℕ (plus 3 1) (plus 1 3) refl
-- ↪ refl : Eq ℕ 4 4
-- --
-- -- 2. Transitivity
-- ------------------
-- --
-- λ» :define TRANS : 𝓤 → 𝓤 = λ A → ∏ (x : A) →
--                                  ∏ (y : A) →
--                                  ∏ (z : A) →
--                                  Eq A x y →
--                                  Eq A y z →
--                                  Eq A x z
-- λ» :define trans
-- : ∀ A → TRANS A
-- = λ A x y z p →
--       J A (λ u v w → Eq A v z → Eq A u z) (λ _ r → r) x y p
-- --
-- λ» :example trans ℕ (plus 1 3) (plus 2 2) (plus 3 1) refl
-- ↪ λ r → r : Eq ℕ 4 4 → Eq ℕ 4 4
-- ∎
--
equivalenceScript :: forall s m. Script s m => m ()
equivalenceScript = do
    section_ "Symmetry"

    define_ "SYM"
        $$ sort_ typeSort ~> sort_ typeSort
        $$ lam_ "A" (pi_ "x" "A" $ pi_ "y" "A" $ Equality "A" "x" "y" ~> Equality "A" "y" "x")

    let j_ u v w a p =  J (V3 (IrrSym u) (IrrSym v) (IrrSym w)) a (abstract3HSym u v w p)

    define_ "sym"
        $$ forall_ "A" ("SYM" @@ "A")
        $$ lams_ ["A","x","y","p"]
            (Inf $ j_ "u" "v" "w" "A" (Equality "A" "v" "u") (lam_ "q" Refl) "x" "y" "p")

    subsection_ "Example"

    define_ "nat-fold"
        $$ forall_ "r" (TermNat ~> ("r" ~> "r") ~> "r" ~> "r")
        $$ lams_ ["r", "n", "s", "z"]
              (Inf $ TermNatElim "_" (liftH "r") "z" (lam_ "l" "s") "n")

    define_ "succ"
        $$ TermNat ~> TermNat
        $$ lam_ "n" (Inf $ TermNatS "n")

    define_ "plus"
        $$ TermNat ~> TermNat ~> TermNat
        $$ lams_ ["x", "y"] ("nat-fold" @@@ TermNat @@ "x" @@ "succ" @@ "y")

    example_ $ Refl -:- Equality TermNat (3 + 1) (1 + 3)
    example_ $ "sym" @@@ TermNat @@ 3 + 1 @@ 1 + 3 @@ Refl

    section_ "Transitivity"

    define_ "TRANS"
        $$ sort_ typeSort ~> sort_ typeSort
        $$ lam_ "A" (pi_ "x" "A" $ pi_ "y" "A" $ pi_ "z" "A" $ Equality "A" "x" "y" ~> Equality "A" "y" "z" ~> Equality "A" "x" "z")

    define_ "trans"
        $$ forall_"A" ("TRANS" @@ "A")
        $$ lams_ ["A","x","y","z","p"]
            (Inf $ j_ "u" "v" "w" "A" (Equality "A" "v" "z" ~> Equality "A" "u" "z") (lams_ ["_", "r"] "r") "x" "y" "p")

    example_ $ "trans" @@@ TermNat @@ 1 + 3 @@ 2 + 2 @@ 3 + 1 @@ Refl

-- |
--
-- >>> runLoud $ spec_ (MartinLof 0) >> inequalityScript
-- -- Proving inequalities is difficult!
-- λ» :define if₁ : ∏ (r : 𝓤₁) → 𝔹 → r → r → r
--                = λ r b t f → 𝔹-elim (λ _ → r) t f b
-- --
-- -- Important thing is to find proper motive for induction
-- λ» :define motive
-- : 𝔹 → 𝔹 → 𝓤 = λ u v → if₁ 𝓤 u (if₁ 𝓤 v ⊤ ⊥) ⊤
-- --
-- -- With proper motive, proof is almost trivial
-- λ» :define true-is-not-false
-- : Eq 𝔹 true false → ⊥
-- = λ p → J 𝔹
--           (λ u v w → motive u v)
--           (λ b → 𝔹-elim (λ c → motive c c) I I b)
--           true
--           false
--           p
-- --
-- λ» :example true-is-not-false
-- ↪ λ p →
--       J 𝔹
--         (λ u v w →
--              𝔹-elim (λ _ → 𝓤) (𝔹-elim (λ _ → 𝓤) ⊤ ⊥ v) ⊤ u)
--         (λ b → 𝔹-elim (λ c → 𝔹-elim (λ _ → 𝓤)
--                                     (𝔹-elim (λ _ → 𝓤) ⊤ ⊥ c)
--                                     ⊤
--                                     c)
--                       I
--                       I
--                       b)
--         true
--         false
--         p
-- : Eq 𝔹 true false → ⊥
-- ∎
--
inequalityScript :: forall s m. Script s m => m ()
inequalityScript = do
    comment_ "Proving inequalities is difficult!"

    define_ "if1"
        $$ pi_ "r" (sort_ typeSortSort) (TermBool ~> "r" ~> "r" ~> "r")
        $$ lams_ ["r", "b", "t", "f"]
              (Inf $ TermBoolElim "_" (liftH "r") "t" "f" "b")

    comment_ "Important thing is to find proper motive for induction"

    let motive u v = "if1" @@ sort_ typeSort @@ u @@ ("if1" @@ sort_ typeSort @@ v @@@ Unit @@@ Empty) @@@ Unit

    define_ "motive"
        $$ TermBool ~> TermBool ~> sort_ typeSort
        $$ lams_ ["u","v"] (motive "u" "v")

    comment_ "With proper motive, proof is almost trivial"
    let j_ u v w a p =  J (V3 (IrrSym u) (IrrSym v) (IrrSym w)) a (abstract3HSym u v w p)

    define_ "true-is-not-false"
        $$ Equality TermBool (Inf TermTrue) (Inf TermFalse) ~> Empty
        $$ lams_ ["p"]
            (Inf $ j_ "u" "v" "w" TermBool
                ("motive" @@ "u" @@  "v")
                (lam_ "b" $ Inf $ TermBoolElim "c" (abstract1HSym "c" $ "motive" @@ "c" @@ "c") (Inf I) (Inf I) "b")
                (Inf TermTrue) (Inf TermFalse) "p")

    example_ "true-is-not-false"

-- |
--
-- >>> runLoud $ spec_ CoCStar >> leibnizScript
-- -- 1. Leibniz
-- -------------
-- --
-- -- We can define Leibniz equality
-- -- in the systems with impredicative bottom universe.
-- -- TODO: define CComega, and make conversions
-- λ» :define Leibniz
-- : ∀ A → A → A → ⋆ = λ A x y → ∏ (C : (A → ⋆)) → C x → C y
-- --
-- -- 1.1. Reflexivity
-- --
-- λ» :define REFL : ⋆ → ⋆ = λ A → ∏ (x : A) → Leibniz A x x
-- λ» :define refl₁ : ∀ A → REFL A = λ A x C Cx → Cx
-- --
-- -- 1.2. Symmetry
-- --
-- λ» :define SYM : ⋆ → ⋆ = λ A → ∏ (x : A) →
--                                ∏ (y : A) →
--                                Leibniz A x y →
--                                Leibniz A y x
-- λ» :define sym
-- : ∀ A → SYM A = λ A x y xy → xy (λ z → Leibniz A z x)
--                                 (refl₁ A x)
-- --
-- -- 1.3. Transitivity
-- --
-- -- An exercise!
-- ∎
--
leibnizScript :: forall s m. Script s m => m ()
leibnizScript = do
    section_ "Leibniz"

    comment_ "We can define Leibniz equality"
    comment_ "in the systems with impredicative bottom universe."
    comment_ "TODO: define CComega, and make conversions"

    define_ "Leibniz"
        $$ pi_ "A" (sort_ typeSort) ("A" ~> "A" ~> sort_ typeSort)
        -- TODO: change last @@ to ~>, improve error message
        $$ lams_ ["A","x","y"] (pi_ "C" ("A" ~> sort_ typeSort) $ "C" @@ "x" ~> "C" @@ "y")

    subsection_ "Reflexivity"

    define_ "REFL"
        $$ sort_ typeSort ~> sort_ typeSort
        $$ lam_ "A" (pi_ "x" "A" $ "Leibniz" @@ "A" @@ "x" @@ "x")

    define_ "refl1"
        $$ forall_ "A" ("REFL" @@ "A")
        $$ lams_ ["A","x","C","Cx"] "Cx"

    subsection_ "Symmetry"

    define_ "SYM"
        $$ sort_ typeSort ~> sort_ typeSort
        $$ lam_ "A" (pi_ "x" "A" $ pi_ "y" "A" $ "Leibniz" @@ "A" @@ "x" @@ "y" ~> "Leibniz" @@ "A" @@ "y" @@ "x")

    define_ "sym"
        $$ forall_ "A" ("SYM" @@ "A")
        $$ lams_ ["A","x","y","xy"]
            ("xy" @@ lam_ "z" ("Leibniz" @@ "A" @@ "z" @@ "x") @@ ("refl1" @@ "A" @@ "x"))

    subsection_ "Transitivity"

    comment_ "An exercise!"

#endif

-- $setup
-- >>> :seti -XOverloadedStrings -XTypeApplications
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Systems
