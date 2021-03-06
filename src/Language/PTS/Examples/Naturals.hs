{-# LANGUAGE OverloadedStrings #-}
module Language.PTS.Examples.Naturals (
#ifdef LANGUAGE_PTS_HAS_NAT
#ifdef LANGUAGE_PTS_HAS_NAT_PRIM
    naturalsPrimScript,
#endif
#endif
    ) where

#ifdef LANGUAGE_PTS_HAS_NAT
#ifdef LANGUAGE_PTS_HAS_NAT_PRIM
import Language.PTS
import Language.PTS.Bound
#endif
#endif

-------------------------------------------------------------------------------
-- Naturals primitive operations
-------------------------------------------------------------------------------

#ifdef LANGUAGE_PTS_HAS_NAT
#ifdef LANGUAGE_PTS_HAS_NAT_PRIM

-- | Primitive operations can be more powerful.
-- This is similar to Boolean example.
--
-- >>> runLoud $ spec_ SysFStar >> naturalsPrimScript
-- -- 1. Constants
-- ---------------
-- --
-- λ» :define succ : ℕ → ℕ = λ n → S n
-- λ» :define zero = 0
-- λ» :define one = succ zero
-- λ» :define two = succ one
-- λ» :define three = succ two
-- --
-- λ» :example zero
-- ↪ 0 : ℕ
-- --
-- λ» :example one
-- ↪ 1 : ℕ
-- --
-- λ» :example two
-- ↪ 2 : ℕ
-- --
-- λ» :example three
-- ↪ 3 : ℕ
-- --
-- -- 2. Using elimination
-- -----------------------
-- --
-- λ» :define nat-fold
-- : ∀ r → ℕ → (r → r) → r → r
-- = λ r n s z → ℕ-elim (λ _ → r) z (λ l → s) n
-- λ» :define plus : ℕ → ℕ → ℕ = λ x y → nat-fold ℕ x succ y
-- --
-- λ» :example plus
-- ↪ λ x y → ℕ-elim (λ _ → ℕ) y (λ l n → S n) x : ℕ → ℕ → ℕ
-- --
-- λ» :example plus two three
-- ↪ 5 : ℕ
-- --
-- λ» :example plus two zero
-- ↪ 2 : ℕ
-- --
-- λ» :example plus zero three
-- ↪ 3 : ℕ
-- --
-- -- 2.1. Partial evaluation
-- --
-- -- Because we scrutinise the first argument, following expressions reduce (well):
-- λ» :example λ n → plus two n : ℕ → ℕ
-- ↪ λ n → S (S n) : ℕ → ℕ
-- --
-- λ» :example λ n → plus zero n : ℕ → ℕ
-- ↪ λ n → n : ℕ → ℕ
-- --
-- -- ... but these doesn't:
-- λ» :example λ n → plus n two : ℕ → ℕ
-- ↪ λ n → ℕ-elim (λ _ → ℕ) 2 (λ l n₁ → S n₁) n : ℕ → ℕ
-- --
-- λ» :example λ n → plus n three : ℕ → ℕ
-- ↪ λ n → ℕ-elim (λ _ → ℕ) 3 (λ l n₁ → S n₁) n : ℕ → ℕ
-- --
-- -- 3. Built-in primitive
-- ------------------------
-- --
-- λ» :define plus# : ℕ → ℕ → ℕ = λ x y → ℕ-plus x y
-- --
-- λ» :example plus#
-- ↪ λ x y → ℕ-plus x y : ℕ → ℕ → ℕ
-- --
-- λ» :example plus# two two
-- ↪ 4 : ℕ
-- --
-- λ» :example plus# two zero
-- ↪ 2 : ℕ
-- --
-- λ» :example plus# zero two
-- ↪ 2 : ℕ
-- --
-- λ» :example plus# zero zero
-- ↪ 0 : ℕ
-- --
-- -- 3.1. Partial evaluation
-- --
-- -- With primitive plus we get more aggressive reduction behaviour
-- λ» :example λ n → plus# two n : ℕ → ℕ
-- ↪ λ n → S (S n) : ℕ → ℕ
-- --
-- λ» :example λ n → plus# zero n : ℕ → ℕ
-- ↪ λ n → n : ℕ → ℕ
-- --
-- λ» :example λ n → plus# n two : ℕ → ℕ
-- ↪ λ n → S (S n) : ℕ → ℕ
-- --
-- λ» :example λ n → plus# n zero : ℕ → ℕ
-- ↪ λ n → n : ℕ → ℕ
-- --
-- -- In fact, literals are extracted "to front":
-- λ» :example λ n m p → plus# (plus# (plus# n one) zero)
--                             (plus# (plus# m two) p)
--                 : ℕ → ℕ → ℕ → ℕ
-- ↪ λ n m p → S (S (S (ℕ-plus n (ℕ-plus m p))))
-- : ℕ → ℕ → ℕ → ℕ
-- --
-- -- 4. With multiplication
-- -------------------------
-- --
-- -- 4.1. Using elimination
-- --
-- λ» :define times
-- : ℕ → ℕ → ℕ = λ x y → nat-fold ℕ x (plus y) zero
-- --
-- λ» :example times two three
-- ↪ 6 : ℕ
-- --
-- -- Because we scrutinise the first argument, following expressions reduce (too well?):
-- λ» :example λ n → times two n : ℕ → ℕ
-- ↪ λ n → ℕ-elim (λ _ → ℕ)
--                (ℕ-elim (λ _ → ℕ) 0 (λ l n₁ → S n₁) n)
--                (λ l n₁ → S n₁)
--                n
-- : ℕ → ℕ
-- --
-- λ» :example λ n → times zero n : ℕ → ℕ
-- ↪ λ n → 0 : ℕ → ℕ
-- --
-- -- ... but these doesn't:
-- λ» :example λ n → times n two : ℕ → ℕ
-- ↪ λ n → ℕ-elim (λ _ → ℕ) 0 (λ l y → S (S y)) n : ℕ → ℕ
-- --
-- λ» :example λ n → times n three : ℕ → ℕ
-- ↪ λ n → ℕ-elim (λ _ → ℕ) 0 (λ l y → S (S (S y))) n : ℕ → ℕ
-- --
-- -- 4.2. Built-in primitive
-- --
-- λ» :define times# : ℕ → ℕ → ℕ = λ x y → ℕ-times x y
-- --
-- λ» :example times# two three
-- ↪ 6 : ℕ
-- --
-- -- With primitive times we get more aggressive reduction behaviour
-- λ» :example λ n → times# three n : ℕ → ℕ
-- ↪ λ n → ℕ-plus n (ℕ-plus n n) : ℕ → ℕ
-- --
-- λ» :example λ n → times# zero n : ℕ → ℕ
-- ↪ λ n → 0 : ℕ → ℕ
-- --
-- λ» :example λ n → times# n three : ℕ → ℕ
-- ↪ λ n → ℕ-plus n (ℕ-plus n n) : ℕ → ℕ
-- --
-- λ» :example λ n → times# n zero : ℕ → ℕ
-- ↪ λ n → 0 : ℕ → ℕ
-- --
-- -- A bit more envolved example:
-- λ» :example λ n → times# (plus# n two) two : ℕ → ℕ
-- ↪ λ n → S (S (S (S (ℕ-plus n n)))) : ℕ → ℕ
-- --
-- -- Lastly: a complex expression with plus# and times#:
-- -- (1 + n) * 1 + 0 + (1 +  m * 2 + m * p)
-- -- Note how the expression is unrolled as much as possible:
-- λ» :example λ n m p →
--                 plus# (plus# (times# (plus# one n) one)
--                              zero)
--                       (plus# (plus# one (times# m two))
--                              (times# m p))
--                 : ℕ → ℕ → ℕ → ℕ
-- ↪ λ n m p → S (S (ℕ-plus n (ℕ-plus (ℕ-plus m m)
--                                    (ℕ-times m p))))
-- : ℕ → ℕ → ℕ → ℕ
-- ∎
--
naturalsPrimScript :: Script s m => m ()
naturalsPrimScript = do
    section_ "Constants"

    define_ "succ"
        $$ TermNat ~> TermNat
        $$ lam_ "n" (Inf $ TermNatS "n")

    defineInf_ "zero"
        $$ TermNatZ

    defineInf_ "one"
        $$ "succ" @@ "zero"

    defineInf_ "two"
        $$ "succ" @@ "one"

    defineInf_ "three"
        $$ "succ" @@ "two"

    example_ "zero"
    example_ "one"
    example_ "two"
    example_ "three"

    section_ "Using elimination"

    define_ "nat-fold"
        $$ forall_ "r" (TermNat ~> ("r" ~> "r") ~> "r" ~> "r")
        $$ lams_ ["r", "n", "s", "z"]
              (Inf $ TermNatElim "_" (liftH "r") "z" (lam_ "l" "s") "n")

    define_ "plus"
        $$ TermNat ~> TermNat ~> TermNat
        $$ lams_ ["x", "y"] ("nat-fold" @@@ TermNat @@ "x" @@ "succ" @@ "y")

    example_ "plus"
    example_ $ "plus" @@ "two" @@ "three"
    example_ $ "plus" @@ "two" @@ "zero"
    example_ $ "plus" @@ "zero" @@ "three"

    subsection_ "Partial evaluation"

    comment_ "Because we scrutinise the first argument, following expressions reduce (well):"
    example_ $ lam_ "n" ("plus" @@ "two" @@ "n")  -:- TermNat ~> TermNat
    example_ $ lam_ "n" ("plus" @@ "zero" @@ "n") -:- TermNat ~> TermNat

    comment_ "... but these doesn't:"
    example_ $ lam_ "n" ("plus" @@ "n" @@ "two")   -:- TermNat ~> TermNat
    example_ $ lam_ "n" ("plus" @@ "n" @@ "three") -:- TermNat ~> TermNat

    section_ "Built-in primitive"

    define_ "plus#"
        $$ TermNat ~> TermNat ~> TermNat
        $$ lams_ ["x", "y"] (Inf (TermPlus "x" "y"))

    example_ "plus#"
    example_ $ "plus#" @@ "two"  @@ "two"
    example_ $ "plus#" @@ "two"  @@ "zero"
    example_ $ "plus#" @@ "zero" @@ "two"
    example_ $ "plus#" @@ "zero" @@ "zero"

    subsection_ "Partial evaluation"

    comment_ "With primitive plus we get more aggressive reduction behaviour"
    example_ $ lam_ "n" ("plus#" @@ "two" @@ "n")  -:- TermNat ~> TermNat
    example_ $ lam_ "n" ("plus#" @@ "zero" @@ "n") -:- TermNat ~> TermNat
    example_ $ lam_ "n" ("plus#" @@ "n" @@ "two")   -:- TermNat ~> TermNat
    example_ $ lam_ "n" ("plus#" @@ "n" @@ "zero" ) -:- TermNat ~> TermNat

    comment_ "In fact, literals are extracted \"to front\":"
    let (.+) :: TermInf s Sym -> TermInf s Sym -> TermInf s Sym
        x .+ y = "plus#" @@ Inf x @@ Inf y

    example_ $ lams_ ["n", "m", "p"]
        (Inf $ ("n" .+ "one") .+ "zero" .+ ("m" .+ "two" .+ "p"))
        -:- TermNat ~> TermNat ~> TermNat ~> TermNat

    section_ "With multiplication"

    subsection_ "Using elimination"

    define_ "times"
        $$ TermNat ~> TermNat ~> TermNat
        $$ lams_ ["x", "y"] ("nat-fold" @@@ TermNat @@ "x" @@ ("plus" @@ "y") @@ "zero")

    example_ $ "times" @@ "two" @@ "three"

    comment_ "Because we scrutinise the first argument, following expressions reduce (too well?):"
    example_ $ lam_ "n" ("times" @@ "two" @@ "n")  -:- TermNat ~> TermNat
    example_ $ lam_ "n" ("times" @@ "zero" @@ "n") -:- TermNat ~> TermNat

    comment_ "... but these doesn't:"
    example_ $ lam_ "n" ("times" @@ "n" @@ "two")   -:- TermNat ~> TermNat
    example_ $ lam_ "n" ("times" @@ "n" @@ "three") -:- TermNat ~> TermNat

    subsection_ "Built-in primitive"

    define_ "times#"
        $$ TermNat ~> TermNat ~> TermNat
        $$ lams_ ["x", "y"] (Inf (TermTimes "x" "y"))

    example_ $ "times#" @@ "two" @@ "three"

    comment_ "With primitive times we get more aggressive reduction behaviour"

    example_ $ lam_ "n" ("times#" @@ "three" @@ "n")  -:- TermNat ~> TermNat
    example_ $ lam_ "n" ("times#" @@ "zero" @@ "n")   -:- TermNat ~> TermNat
    example_ $ lam_ "n" ("times#" @@ "n" @@ "three")  -:- TermNat ~> TermNat
    example_ $ lam_ "n" ("times#" @@ "n" @@ "zero" )  -:- TermNat ~> TermNat

    comment_ "A bit more envolved example:"
    example_ $ lam_ "n" ("times#" @@ ("plus#" @@ "n" @@ "two") @@ "two") -:- TermNat ~> TermNat

    comment_ "Lastly: a complex expression with plus# and times#:"
    let (.*) :: TermInf s Sym -> TermInf s Sym -> TermInf s Sym
        x .* y = "times#" @@ Inf x @@ Inf y

    comment_ "(1 + n) * 1 + 0 + (1 +  m * 2 + m * p)"
    comment_ "Note how the expression is unrolled as much as possible:"
    example_ $ lams_ ["n", "m", "p"]
        (Inf $ (("one" .+ "n") .* "one") .+ "zero" .+ ("one" .+ ("m" .* "two") .+ ("m" .* "p")))
        -:- TermNat ~> TermNat ~> TermNat ~> TermNat
#endif
#endif

-- $setup
-- >>> :seti -XOverloadedStrings -XTypeApplications
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Systems
