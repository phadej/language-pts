#ifdef LANGUAGE_PTS_HAS_EQUALITY
#ifdef LANGUAGE_PTS_HAS_BOOL
#ifdef LANGUAGE_PTS_HAS_NAT
#ifdef LANGUAGE_PTS_HAS_SIGMA
#ifdef LANGUAGE_PTS_HAS_PROP
#define EQUALITY_EXAMPLES
{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
#endif
#endif
#endif
#endif
#endif
module Language.PTS.Examples.EvenOrOdd (
#ifdef EQUALITY_EXAMPLES
    evenOrOddScript,
#endif
    ) where

#ifdef EQUALITY_EXAMPLES
import Language.PTS
import Language.PTS.Bound

-- |
--
-- >>> runLoud $ spec_ (MartinLof 0) >> evenOrOddScript
-- -- 1. double
-- ------------
-- --
-- λ» :define succ : ℕ → ℕ = λ n → S n
-- λ» :define double
-- : ℕ → ℕ = λ n → ℕ-elim (λ _ → ℕ) 0 (λ _ m → succ (succ m)) n
-- --
-- λ» :example double 0
-- ↪ 0 : ℕ
-- --
-- λ» :example double 1
-- ↪ 2 : ℕ
-- --
-- λ» :example double 5
-- ↪ 10 : ℕ
-- --
-- -- 2. Even
-- ----------
-- --
-- λ» :define Even
-- : ℕ → 𝓤 = λ n → ∑ (m : ℕ) → Eq ℕ n (double m)
-- λ» :define zero-is-even : Even 0 = pair 0 refl
-- --
-- λ» :example pair 1 refl : Even 2
-- ↪ pair 1 refl
-- : ∑ (m : ℕ) →
--   Eq ℕ 2 (ℕ-elim (λ _ → ℕ) 0 (λ _ m → S (S m)) m)
-- --
-- -- 3. Odd
-- ---------
-- --
-- λ» :define Odd
-- : ℕ → 𝓤 = λ n → ∑ (m : ℕ) → Eq ℕ n (S (double m))
-- --
-- λ» :example pair 3 refl : Odd 7
-- ↪ pair 3 refl
-- : ∑ (m : ℕ) →
--   Eq ℕ 7 (S (ℕ-elim (λ _ → ℕ) 0 (λ _ m → S (S m)) m))
-- --
-- -- 4. Congruence
-- ----------------
-- --
-- λ» :define congruence
-- : ∀ A →
--   ∀ B →
--   ∏ (f : (A → B)) →
--   ∏ (x : A) →
--   ∏ (y : A) →
--   Eq A x y →
--   Eq B (f x) (f y)
-- = λ A B f x y p →
--       J A (λ u v _ → Eq B (f u) (f v)) (λ _ → refl) x y p
-- --
-- -- 5. Succ Even is Odd
-- ----------------------
-- --
-- λ» :define succ-even-is-odd
-- : ∏ (n : ℕ) → Even n → Odd (S n)
-- = λ n even-n →
--       match even-n
--             (λ m proof →
--                  pair m (congruence
--                              ℕ ℕ succ n (double m) proof))
-- λ» :define succ-odd-is-even
-- : ∏ (n : ℕ) → Odd n → Even (S n)
-- = λ n odd-n →
--       match
--           odd-n
--           (λ m proof →
--                pair
--                    (succ m)
--                    (congruence
--                         ℕ ℕ succ n (succ (double m)) proof))
-- --
-- -- 6. Boolean
-- -------------
-- --
-- λ» :define if₁ : ∏ (r : 𝓤₁) → 𝔹 → r → r → r
--                = λ r b t f → 𝔹-elim (λ _ → r) t f b
-- --
-- -- 7. Either
-- ------------
-- --
-- -- 7.1. Type
-- --
-- λ» :define Either
-- : 𝓤 → 𝓤 → 𝓤 = λ A B → ∑ (t : 𝔹) → if₁ 𝓤 t A B
-- --
-- -- 7.2. Constructors
-- --
-- λ» :define left : ∀ A → ∀ B → A → Either A B
--                 = λ A B x → pair true x
-- λ» :define right : ∀ A → ∀ B → B → Either A B
--                  = λ A B y → pair false y
-- --
-- -- 7.3. Non-dependent elimination
-- --
-- λ» :define either
-- : ∀ A → ∀ B → ∀ C → (A → C) → (B → C) → Either A B → C
-- = λ A B C f g e →
--       match e (λ t v → (𝔹-elim (λ t₁ → if₁ 𝓤 t₁ A B → C)
--                                (λ x → f x)
--                                (λ y → g y)
--                                t)
--                            v)
-- --
-- -- 8. All number are either even or odd
-- ---------------------------------------
-- --
-- λ» :define theorem
-- : ∏ (n : ℕ) → Either (Even n) (Odd n)
-- = λ n →
--       ℕ-elim
--           (λ m → Either (Even m) (Odd m))
--           (pair true zero-is-even)
--           (λ l H →
--                either
--                    (Even l)
--                    (Odd l)
--                    (Either (Even (succ l)) (Odd (succ l)))
--                    (λ p → pair false (succ-even-is-odd l p))
--                    (λ p → pair true (succ-odd-is-even l p))
--                    H)
--           n
-- --
-- λ» :example theorem 0
-- ↪ pair true (pair 0 refl)
-- : ∑ (t : 𝔹) →
--   𝔹-elim
--       (λ _ → 𝓤)
--       (∑ (m : ℕ) →
--        Eq ℕ 0 (ℕ-elim (λ _ → ℕ) 0 (λ _ m → S (S m)) m))
--       (∑ (m : ℕ) →
--        Eq ℕ 0 (S (ℕ-elim (λ _ → ℕ) 0 (λ _ m → S (S m)) m)))
--       t
-- --
-- λ» :example theorem 100
-- ↪ pair true (pair 50 refl)
-- : ∑ (t : 𝔹) →
--   𝔹-elim
--       (λ _ → 𝓤)
--       (∑ (m : ℕ) →
--        Eq ℕ 100 (ℕ-elim (λ _ → ℕ) 0 (λ _ m → S (S m)) m))
--       (∑ (m : ℕ) →
--        Eq ℕ 100 (S (ℕ-elim
--                         (λ _ → ℕ) 0 (λ _ m → S (S m)) m)))
--       t
-- --
-- λ» :example theorem 113
-- ↪ pair false (pair 56 refl)
-- : ∑ (t : 𝔹) →
--   𝔹-elim
--       (λ _ → 𝓤)
--       (∑ (m : ℕ) →
--        Eq ℕ 113 (ℕ-elim (λ _ → ℕ) 0 (λ _ m → S (S m)) m))
--       (∑ (m : ℕ) →
--        Eq ℕ 113 (S (ℕ-elim
--                         (λ _ → ℕ) 0 (λ _ m → S (S m)) m)))
--       t
-- ∎
--
evenOrOddScript :: forall s m. Script s m => m ()
evenOrOddScript = do
    section_ "double"

    define_ "succ"
        $$ TermNat ~> TermNat
        $$ lam_ "n" (Inf $ TermNatS "n")
    

    define_ "double"
        $$ TermNat ~> TermNat
        $$ lam_ "n" (Inf $ TermNatElim "_" (liftH TermNat)
            (Inf TermNatZ)
            (lams_ ["_","m"] ("succ" @@ ("succ" @@ "m")))
            "n")

    example_ $ "double" @@ 0
    example_ $ "double" @@ 1
    example_ $ "double" @@ 5

    section_ "Even"

    define_ "Even"
        $$ TermNat ~> sort_ typeSort
        $$ lam_ "n" (Inf $ Sigma "m" TermNat $ abstract1HSym "m" $ 
            Equality TermNat "n" ("double" @@ "m"))

    define_ "zero-is-even"
        $$ "Even" @@ 0
        $$ Pair 0 Refl
        
    example_ $$ Pair 1 Refl -:- "Even" @@ 2

    section_ "Odd"
      
    define_ "Odd"
        $$ TermNat ~> sort_ typeSort
        $$ lam_ "n" (Inf $ Sigma "m" TermNat $ abstract1HSym "m" $ 
            Equality TermNat "n" (Inf $ TermNatS $ "double" @@ "m"))

    example_ $$ Pair 3 Refl -:- "Odd" @@ 7

    let j_ u v w a p =  J (V3 (IrrSym u) (IrrSym v) (IrrSym w)) a (abstract3HSym u v w p)

    section_ "Congruence"

    define_ "congruence"
        $$ foralls_ ["A","B"] (pi_ "f" ("A"~> "B") $ pi_ "x" "A" $ pi_ "y" "A"
            $ Equality "A" "x" "y" ~> Equality "B" ("f" @@ "x") ("f" @@ "y"))
        $$ lams_ ["A","B","f","x","y","p"]
            (Inf $ j_ "u" "v" "_" "A" (Equality "B" ("f" @@ "u") ("f" @@ "v")) (lam_ "_" Refl) "x" "y" "p")

    section_ "Succ Even is Odd"

    define_ "succ-even-is-odd"
        $$ pi_ "n" TermNat ("Even" @@ "n" ~> "Odd" @@ (Inf $ TermNatS $ "n"))
        $$ lams_ ["n","even-n"] (Match "even-n" "m" "proof"
            $ abstract2HSym "m" "proof"
            $ Pair "m" $ "congruence" @@@ TermNat @@@ TermNat @@ "succ" @@ "n" @@ ("double" @@ "m") @@ "proof")

    define_ "succ-odd-is-even"
        $$ pi_ "n" TermNat ("Odd" @@ "n" ~> "Even" @@ (Inf $ TermNatS $ "n"))
        $$ lams_ ["n","odd-n"] (Match "odd-n" "m" "proof"
            $ abstract2HSym "m" "proof"
            $ Pair ("succ" @@ "m") $ "congruence" @@@ TermNat @@@ TermNat @@ "succ" @@ "n" @@ ("succ" @@ ("double" @@ "m")) @@ "proof")

    section_ "Boolean"

    define_ "if1"
        $$ pi_ "r" (sort_ typeSortSort) (TermBool ~> "r" ~> "r" ~> "r")
        $$ lams_ ["r", "b", "t", "f"]
              (Inf $ TermBoolElim "_" (liftH "r") "t" "f" "b")


    section_ "Either"

    subsection_ "Type"

    define_ "Either"
        $$ sort_ typeSort ~> sort_ typeSort ~> sort_ typeSort
        $$ lams_ ["A", "B"] (Inf $ Sigma "t" TermBool $ abstract1HSym "x" $ "if1" @@ sort_ typeSort @@ "x" @@ "A" @@ "B")

    subsection_ "Constructors"

    define_ "left"
        $$ foralls_ ["A", "B"] ("A" ~> "Either" @@ "A" @@ "B")
        $$ lams_ ["A","B","x"] (Pair (Inf TermTrue) "x")

    define_ "right"
        $$ foralls_ ["A", "B"] ("B" ~> "Either" @@ "A" @@ "B")
        $$ lams_ ["A","B","y"] (Pair (Inf TermFalse) "y")

    subsection_ "Non-dependent elimination"

    let eitherBody :: TermInf s Sym
        eitherBody = TermBoolElim
            "t" (abstract1HSym "t" $ "if1" @@ sort_ typeSort @@ "t" @@ "A" @@ "B" ~> "C")
            (lam_ "x" $ "f" @@ "x")
            (lam_ "y" $ "g" @@ "y")
            "t"

    define_ "either"
        $$ foralls_ ["A","B","C"] (("A" ~> "C") ~> ("B" ~> "C") ~> "Either" @@ "A" @@ "B" ~> "C")
        $$ lams_ ["A","B","C","f","g","e"]
            (Match "e" "t" "v" $ abstract2HSym "t" "v" $ eitherBody @@ "v")


    section_ "All number are either even or odd"

    let motive :: TermChk s Sym -> TermInf s Sym
        motive n = "Either" @@ ("Even" @@ n) @@ ("Odd" @@ n)

    define_ "theorem"
        $$ pi_ "n" TermNat (motive "n")
        $$ lam_ "n" (Inf $ TermNatElim "m" (abstract1HSym "m" $ motive "m")
            (Pair (Inf TermTrue) $ "zero-is-even")
            (lams_ ["l","H"] (Inf $ apps_ "either"
                [ "Even" @@ "l"
                , "Odd" @@ "l"
                , Inf (motive (Inf $ "succ" @@ "l"))
                , lam_ "p" $ Pair (Inf TermFalse) $ "succ-even-is-odd" @@ "l" @@ "p"
                , lam_ "p" $ Pair (Inf TermTrue)  $ "succ-odd-is-even" @@ "l" @@ "p"
                , "H"
                ]))
            "n")

    example_ $ "theorem" @@ 0
    example_ $ "theorem" @@ 100
    example_ $ "theorem" @@ 113

-- $setup
-- >>> :seti -XOverloadedStrings -XTypeApplications
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Systems
#endif
