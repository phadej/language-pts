{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
#ifdef LANGUAGE_PTS_HAS_SIGMA
#ifdef LANGUAGE_PTS_HAS_BOOL
#ifdef LANGUAGE_PTS_HAS_NAT
#define SIGMA_EXAMPLES
#endif
#endif
#endif
module Language.PTS.Examples.Sigma (
#ifdef SIGMA_EXAMPLES
    eitherScript,
    pairScript,
#endif
    ) where

#ifdef SIGMA_EXAMPLES
import Language.PTS
import Language.PTS.Bound

-- |
--
-- >>> runLoud $ spec_ (MartinLof 0) >> eitherScript
-- -- If we have Booleans and dependent pair, we can make Either
-- --
-- -- 1. Boolean prelude
-- ---------------------
-- --
-- λ» :define if : ∀ r → 𝔹 → r → r → r
--               = λ r b t f → 𝔹-elim (λ _ → r) t f b
-- --
-- -- We a need variant in higher universe too
-- λ» :define if₁ : ∏ (r : 𝓤₁) → 𝔹 → r → r → r
--                = λ r b t f → 𝔹-elim (λ _ → r) t f b
-- --
-- -- 2. Type
-- ----------
-- --
-- λ» :define Either
-- : 𝓤 → 𝓤 → 𝓤 = λ A B → ∑ (t : 𝔹) → if₁ 𝓤 t A B
-- --
-- -- 2.1. Example
-- --
-- λ» :define A = Either 𝔹 ℕ
-- --
-- λ» :example A
-- ↪ ∑ (t : 𝔹) → 𝔹-elim (λ _ → 𝓤) 𝔹 ℕ t : 𝓤
-- --
-- -- 3. Constructors
-- ------------------
-- --
-- λ» :define left : ∀ A → ∀ B → A → Either A B
--                 = λ A B x → pair true x
-- λ» :define right : ∀ A → ∀ B → B → Either A B
--                  = λ A B y → pair false y
-- --
-- -- 3.1. Examples
-- --
-- λ» :define x : A = left 𝔹 ℕ true
-- λ» :define y : A = left 𝔹 ℕ false
-- λ» :define u : A = right 𝔹 ℕ 1
-- λ» :define v : A = right 𝔹 ℕ 2
-- --
-- λ» :example x
-- ↪ pair true true : ∑ (t : 𝔹) → 𝔹-elim (λ _ → 𝓤) 𝔹 ℕ t
-- --
-- λ» :example y
-- ↪ pair true false : ∑ (t : 𝔹) → 𝔹-elim (λ _ → 𝓤) 𝔹 ℕ t
-- --
-- λ» :example u
-- ↪ pair false 1 : ∑ (t : 𝔹) → 𝔹-elim (λ _ → 𝓤) 𝔹 ℕ t
-- --
-- λ» :example v
-- ↪ pair false 2 : ∑ (t : 𝔹) → 𝔹-elim (λ _ → 𝓤) 𝔹 ℕ t
-- --
-- -- 4. Non-dependent elimination
-- -------------------------------
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
-- -- 4.1. Example
-- --
-- λ» :define boolToNat : 𝔹 → ℕ = λ b → if ℕ b 0 1
-- λ» :define toNat
-- : A → ℕ = either 𝔹 ℕ ℕ boolToNat (λ n → S n)
-- --
-- λ» :example toNat x
-- ↪ 0 : ℕ
-- --
-- λ» :example toNat y
-- ↪ 1 : ℕ
-- --
-- λ» :example toNat u
-- ↪ 2 : ℕ
-- --
-- λ» :example toNat v
-- ↪ 3 : ℕ
-- --
-- -- 5. Reduction
-- ---------------
-- --
-- -- Note how much type annotations we don't have to write in Haskell
-- λ» :define redex₁
-- : ∀ A → ∀ B → ∀ C → (A → C) → (B → C) → A → C
-- = λ A B C f g x → either A B C f g (left A B x)
-- --
-- -- it reduces!
-- λ» :example redex₁
-- ↪ λ A B C f g x → f x
-- : ∀ A → ∀ B → ∀ C → (A → C) → (B → C) → A → C
-- --
-- λ» :define redex₂
-- : ∀ A → ∀ B → ∀ C → (A → C) → (B → C) → B → C
-- = λ A B C f g y → either A B C f g (right A B y)
-- --
-- λ» :example redex₂
-- ↪ λ A B C f g y → g y
-- : ∀ A → ∀ B → ∀ C → (A → C) → (B → C) → B → C
-- ∎
--
eitherScript :: forall s m. Script s m => m ()
eitherScript = do
    let one = TermNatS (Inf TermNatZ)
    let two = TermNatS (Inf one)

    comment_ "If we have Booleans and dependent pair, we can make Either"

    section_ "Boolean prelude"

    define_ "if"
        $$ forall_ "r" (TermBool ~> "r" ~> "r" ~> "r")
        $$ lams_ ["r", "b", "t", "f"]
              (Inf $ TermBoolElim "_" (liftH "r") "t" "f" "b")

    comment_ "We a need variant in higher universe too"
    define_ "if1"
        $$ pi_ "r" (sort_ typeSortSort) (TermBool ~> "r" ~> "r" ~> "r")
        $$ lams_ ["r", "b", "t", "f"]
              (Inf $ TermBoolElim "_" (liftH "r") "t" "f" "b")

    section_ "Type"

    define_ "Either"
        $$ sort_ typeSort ~> sort_ typeSort ~> sort_ typeSort
        $$ lams_ ["A", "B"] (Inf $ Sigma "t" TermBool $ abstract1HSym "x" $ "if1" @@ sort_ typeSort @@ "x" @@ "A" @@ "B")

    subsection_ "Example"

    defineInf_ "A" $ "Either" @@@ TermBool @@@ TermNat
    example_ "A"

    section_ "Constructors"

    define_ "left"
        $$ foralls_ ["A", "B"] ("A" ~> "Either" @@ "A" @@ "B")
        $$ lams_ ["A","B","x"] (Pair (Inf TermTrue) "x")

    define_ "right"
        $$ foralls_ ["A", "B"] ("B" ~> "Either" @@ "A" @@ "B")
        $$ lams_ ["A","B","y"] (Pair (Inf TermFalse) "y")

    subsection_ "Examples"

    define_ "x"
        $$ "A"
        $$ "left" @@@ TermBool @@@ TermNat @@@ TermTrue
    define_ "y"
        $$ "A"
        $$ "left" @@@ TermBool @@@ TermNat @@@ TermFalse
    define_ "u"
        $$ "A"
        $$ "right" @@@ TermBool @@@ TermNat @@@ one
    define_ "v"
        $$ "A"
        $$ "right" @@@ TermBool @@@ TermNat @@@ two

    example_ "x"
    example_ "y"
    example_ "u"
    example_ "v"

    section_ "Non-dependent elimination"

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

    subsection_ "Example"

    define_ "boolToNat"
        $$ TermBool ~> TermNat
        $$ lam_ "b" ("if" @@@ TermNat @@ "b" @@ Inf TermNatZ @@ Inf one)

    define_ "toNat"
        $$ "A" ~> TermNat
        $$ "either" @@@ TermBool @@@ TermNat @@@ TermNat
            @@ "boolToNat"
            @@ lam_ "n" (Inf $ TermNatS "n")

    example_ $ "toNat" @@ "x"
    example_ $ "toNat" @@ "y"
    example_ $ "toNat" @@ "u"
    example_ $ "toNat" @@ "v"

    section_ "Reduction"

    comment_ "Note how much type annotations we don't have to write in Haskell"
    
    define_ "redex1"
        $$ foralls_ ["A","B","C"] (("A" ~> "C") ~> ("B" ~> "C") ~> "A" ~> "C")
        $$ lams_ ["A","B","C","f","g","x"] ("either" @@ "A" @@ "B" @@ "C" @@ "f" @@ "g" @@ ("left" @@ "A" @@ "B" @@ "x"))

    comment_ "it reduces!"
    example_ "redex1"

    define_ "redex2"
        $$ foralls_ ["A","B","C"] (("A" ~> "C") ~> ("B" ~> "C") ~> "B" ~> "C")
        $$ lams_ ["A","B","C","f","g","y"] ("either" @@ "A" @@ "B" @@ "C" @@ "f" @@ "g" @@ ("right" @@ "A" @@ "B" @@ "y"))

    example_ "redex2"

-- |
--
-- >>> runLoud $ spec_ (MartinLof 0) >> pairScript
-- -- Non dependent pair
-- --
-- -- 1. Type
-- ----------
-- --
-- λ» :define Pair : 𝓤 → 𝓤 → 𝓤 = λ A B → ∑ (_ : A) → B
-- --
-- -- 2. Constructor
-- -----------------
-- --
-- λ» :define mkPair : ∀ A → ∀ B → A → B → Pair A B
--                   = λ A B x y → pair x y
-- --
-- -- 3. Projections
-- -----------------
-- --
-- λ» :define fst : ∀ A → ∀ B → Pair A B → A
--                = λ A B p → match p (λ x y → x)
-- λ» :define snd : ∀ A → ∀ B → Pair A B → B
--                = λ A B p → match p (λ x y → y)
-- --
-- -- 4. Reduction
-- ---------------
-- --
-- λ» :define redex₁ : ∀ A → ∀ B → A → B → A
--                   = λ A B x y → fst A B (mkPair A B x y)
-- --
-- λ» :example redex₁
-- ↪ λ A B x y → x : ∀ A → ∀ B → A → B → A
-- --
-- λ» :define redex₂ : ∀ A → ∀ B → A → B → B
--                   = λ A B x y → snd A B (mkPair A B x y)
-- --
-- λ» :example redex₂
-- ↪ λ A B x y → y : ∀ A → ∀ B → A → B → B
-- ∎
--
pairScript :: forall s m. Script s m => m ()
pairScript = do
    comment_ "Non dependent pair"

    section_ "Type"

    define_ "Pair"
        $$ sort_ typeSort ~> sort_ typeSort ~> sort_ typeSort
        $$ lams_ ["A", "B"] (Inf $ Sigma "_" "A" $ liftH "B")

    section_ "Constructor"

    define_ "mkPair"
        $$ foralls_ ["A","B"] ("A" ~> "B" ~> "Pair" @@ "A" @@ "B")
        $$ lams_ ["A","B","x","y"] (Pair "x" "y")

    section_ "Projections"

    define_ "fst"
        $$ foralls_ ["A","B"] ("Pair" @@ "A" @@ "B" ~> "A")
        $$ lams_ ["A","B","p"] (Match "p" "x" "y" $ abstract2HSym "x" "y" "x")

    define_ "snd"
        $$ foralls_ ["A","B"] ("Pair" @@ "A" @@ "B" ~> "B")
        $$ lams_ ["A","B","p"] (Match "p" "x" "y" $ abstract2HSym "x" "y" "y")

    section_ "Reduction"

    define_ "redex1"
        $$ foralls_ ["A","B"] ("A" ~> "B" ~> "A")
        $$ lams_ ["A","B","x","y"] ("fst" @@ "A" @@ "B" @@ ("mkPair" @@ "A" @@ "B" @@ "x" @@ "y"))

    example_ "redex1"

    define_ "redex2"
        $$ foralls_ ["A","B"] ("A" ~> "B" ~> "B")
        $$ lams_ ["A","B","x","y"] ("snd" @@ "A" @@ "B" @@ ("mkPair" @@ "A" @@ "B" @@ "x" @@ "y"))

    example_ "redex2"

#endif

-- $setup
-- >>> :seti -XOverloadedStrings -XTypeApplications
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Systems
