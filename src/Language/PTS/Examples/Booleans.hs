{-# LANGUAGE OverloadedStrings #-}
module Language.PTS.Examples.Booleans (
    churchBooleansScript,
#ifdef LANGUAGE_PTS_HAS_BOOL
#ifdef LANGUAGE_PTS_HAS_NAT
    booleansScript,
#endif
#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM
    booleansPrimScript,
#endif
#endif

    ) where

import Language.PTS

#if defined(LANGUAGE_PTS_HAS_BOOL) && defined(LANGUAGE_PTS_HAS_NAT)
import Language.PTS.Bound
#endif

-------------------------------------------------------------------------------
-- Church Booleans
-------------------------------------------------------------------------------

-- | 'SystemF' is powerful enough to define Church Booleans.
--
-- >>> runLoud $ spec_ SysFStar >> churchBooleansScript
-- -- 1. Definitions
-- -----------------
-- --
-- λ» :define Bool : ⋆ = ∀ r → r → r → r
-- λ» :define True : Bool = λ r t f → t
-- λ» :define False : Bool = λ r t f → f
-- --
-- -- 2. Functions
-- ---------------
-- --
-- -- Bool values are itself an if statement
-- λ» :define not : Bool → Bool = λ x → x Bool False True
-- λ» :define and : Bool → Bool → Bool = λ x y → x Bool y False
-- --
-- -- 3. Examples
-- --------------
-- --
-- -- One have to look carefully to distinguish the results :)
-- λ» :example and True True
-- ↪ λ r t f → t : ∀ r → r → r → r
-- --
-- λ» :example and True False
-- ↪ λ r t f → f : ∀ r → r → r → r
-- --
-- λ» :example and False True
-- ↪ λ r t f → f : ∀ r → r → r → r
-- --
-- -- 4. Extras
-- ------------
-- --
-- -- Note the usage of impredicativity.
-- λ» :example not
-- ↪ λ x → x (∀ r → r → r → r) (λ r t f → f) (λ r t f → t)
-- : (∀ r → r → r → r) → ∀ r → r → r → r
-- --
-- λ» :example and
-- ↪ λ x y → x (∀ r → r → r → r) y (λ r t f → f)
-- : (∀ r → r → r → r) → (∀ r → r → r → r) → ∀ r → r → r → r
-- ∎
--
churchBooleansScript :: Script s m => m ()
churchBooleansScript = do
    section_ "Definitions"

    define_ "Bool"
        $$ sort_ typeSort
        $$ forall_ "r" ("r" ~> "r" ~> "r")

    define_ "True"
        $$ "Bool"
        $$ lams_ ["r", "t", "f"] "t"

    define_ "False"
        $$ "Bool"
        $$ lams_ ["r", "t", "f"] "f"

    section_ "Functions"

    comment_ "Bool values are itself an if statement"
    define_ "not"
        $$ "Bool" ~> "Bool"
        $$ lam_ "x" ("x" @@ "Bool" @@ "False" @@ "True")

    define_ "and"
        $$ "Bool" ~> "Bool" ~> "Bool"
        $$ lams_ ["x", "y"] ("x" @@ "Bool" @@ "y" @@ "False")

    section_ "Examples"

    comment_ "One have to look carefully to distinguish the results :)"
    example_ $ "and" @@ "True"  @@ "True"
    example_ $ "and" @@ "True"  @@ "False"
    example_ $ "and" @@ "False" @@ "True"

    section_ "Extras"
    comment_ "Note the usage of impredicativity."

    example_ "not"
    example_ "and"

#if defined(LANGUAGE_PTS_HAS_BOOL) && defined(LANGUAGE_PTS_HAS_NAT)
-------------------------------------------------------------------------------
-- Built-in Booleans
-------------------------------------------------------------------------------

-- | Examples of built-in Booleans.
-- We need dependent types to be able to use dependent @𝔹-elim@.
--
-- >>> runLoud $ spec_ (MartinLof 0) >> booleansScript
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
--               = λ r b t f → 𝔹-elim (λ _ → r) t f b
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
-- : Π (b : 𝔹) → 𝔹-elim (λ _ → 𝓤) 𝔹 ℕ b
-- = λ b → 𝔹-elim (λ p → 𝔹-elim (λ _ → 𝓤) 𝔹 ℕ p) true 0 b
-- --
-- λ» :example contrived
-- ↪ λ b → 𝔹-elim (λ p → 𝔹-elim (λ _ → 𝓤) 𝔹 ℕ p) true 0 b
-- : Π (b : 𝔹) → 𝔹-elim (λ _ → 𝓤) 𝔹 ℕ b
-- --
-- λ» :example contrived true
-- ↪ true : 𝔹
-- --
-- λ» :example contrived false
-- ↪ 0 : ℕ
-- ∎
--
booleansScript :: Script s m => m ()
booleansScript = do
    section_ "Constants"

    example_ TermBool
    example_ TermTrue
    example_ TermFalse

    section_ "Non-dependent elimination: if"

    define_ "if"
        $$ forall_ "r" (TermBool ~> "r" ~> "r" ~> "r")
        $$ lams_ ["r", "b", "t", "f"]
              (Inf $ TermBoolElim "_" (liftH "r") "t" "f" "b")

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

    let ty = TermBoolElim "_" (liftH $ sort_ typeSort) (Inf TermBool) (Inf TermNat) "b"
    define_ "contrived"
        $$ pi_ "b" TermBool
              (TermBoolElim "_" (liftH $ sort_ typeSort) (Inf TermBool) (Inf TermNat) "b")
        $$ lam_ "b"
            (Inf $ TermBoolElim "p" (abstract1HSym "b" ty) (Inf TermTrue) (Inf TermNatZ)  "b")

    example_ "contrived"
    example_ $ "contrived" @@@ TermTrue
    example_ $ "contrived" @@@ TermFalse
#endif

-------------------------------------------------------------------------------
-- Boolean primitive operations
-------------------------------------------------------------------------------

#ifdef LANGUAGE_PTS_HAS_BOOL
#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM

-- | Primitive operations can be more powerful.
--
-- Note how we defined the 'Value':
--
-- @
-- data 'ValueIntro' err s a
--     ...
--     | 'ValueTrue'
--     | 'ValueFalse'
--     ...
--
-- data 'ValueElim' err s a
--     ...
--     | 'ValueAnd' ('ValueElim' err s a) ('ValueElim' err s a)
--     ...
-- @
--
-- By /construction/, there cannot be literal Boolean in evaluated 'ValueAnd'.
-- Following script demonstrates this functionality:
--
-- >>> runLoud $ spec_ SysFStar >> booleansPrimScript
-- -- 1. Using elimination
-- -----------------------
-- --
-- λ» :define if : ∀ r → 𝔹 → r → r → r
--               = λ r b t f → 𝔹-elim (λ _ → r) t f b
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
-- -- 1.1. Partial evaluation
-- --
-- -- Because we scrutinise the first argument, following expressions reduce (well):
-- λ» :example λ b → and true b : 𝔹 → 𝔹
-- ↪ λ b → b : 𝔹 → 𝔹
-- --
-- λ» :example λ b → and false b : 𝔹 → 𝔹
-- ↪ λ b → false : 𝔹 → 𝔹
-- --
-- -- ... but these doesn't:
-- λ» :example λ b → and b true : 𝔹 → 𝔹
-- ↪ λ b → 𝔹-elim (λ _ → 𝔹) true false b : 𝔹 → 𝔹
-- --
-- λ» :example λ b → and b false : 𝔹 → 𝔹
-- ↪ λ b → 𝔹-elim (λ _ → 𝔹) false false b : 𝔹 → 𝔹
-- --
-- -- 2. Built-in primitive
-- ------------------------
-- --
-- λ» :define and# : 𝔹 → 𝔹 → 𝔹 = λ x y → 𝔹-and x y
-- --
-- λ» :example and#
-- ↪ λ x y → 𝔹-and x y : 𝔹 → 𝔹 → 𝔹
-- --
-- λ» :example and# true true
-- ↪ true : 𝔹
-- --
-- λ» :example and# true false
-- ↪ false : 𝔹
-- --
-- λ» :example and# false true
-- ↪ false : 𝔹
-- --
-- λ» :example and# false false
-- ↪ false : 𝔹
-- --
-- -- 2.1. Partial evaluation
-- --
-- -- With primitive and we get more aggressive reduction behaviour
-- λ» :example λ b → and# true b : 𝔹 → 𝔹
-- ↪ λ b → b : 𝔹 → 𝔹
-- --
-- λ» :example λ b → and# false b : 𝔹 → 𝔹
-- ↪ λ b → false : 𝔹 → 𝔹
-- --
-- λ» :example λ b → and# b true : 𝔹 → 𝔹
-- ↪ λ b → b : 𝔹 → 𝔹
-- --
-- λ» :example λ b → and# b false : 𝔹 → 𝔹
-- ↪ λ b → false : 𝔹 → 𝔹
-- --
-- -- In fact, literal cannot be in evaluated and-expression:
-- λ» :example λ x y z → and# (and# x true)
--                            (and# (and# y true) z)
--                 : 𝔹 → 𝔹 → 𝔹 → 𝔹
-- ↪ λ x y z → 𝔹-and x (𝔹-and y z) : 𝔹 → 𝔹 → 𝔹 → 𝔹
-- --
-- λ» :example λ x y z → and# (and# x false)
--                            (and# (and# y true) z)
--                 : 𝔹 → 𝔹 → 𝔹 → 𝔹
-- ↪ λ x y z → false : 𝔹 → 𝔹 → 𝔹 → 𝔹
-- ∎
--
booleansPrimScript :: Script s m => m ()
booleansPrimScript = do
    section_ "Using elimination"

    define_ "if"
        $$ forall_ "r" (TermBool ~> "r" ~> "r" ~> "r")
        $$ lams_ ["r", "b", "t", "f"]
              (Inf $ TermBoolElim "_" (liftH "r") "t" "f" "b")

    define_ "and"
        $$ TermBool ~> TermBool ~> TermBool
        $$ lams_ ["x", "y"] ("if" @@@ TermBool @@ "x" @@ "y" @@@ TermFalse)

    example_ "and"
    example_ $ "and" @@@ TermTrue  @@@ TermTrue
    example_ $ "and" @@@ TermTrue  @@@ TermFalse
    example_ $ "and" @@@ TermFalse @@@ TermTrue
    example_ $ "and" @@@ TermFalse @@@ TermFalse

    subsection_ "Partial evaluation"

    comment_ "Because we scrutinise the first argument, following expressions reduce (well):"
    example_ $ lam_ "b" ("and" @@@ TermTrue @@ "b")  -:- TermBool ~> TermBool
    example_ $ lam_ "b" ("and" @@@ TermFalse @@ "b") -:- TermBool ~> TermBool

    comment_ "... but these doesn't:"
    example_ $ lam_ "b" ("and" @@ "b" @@@ TermTrue)   -:- TermBool ~> TermBool
    example_ $ lam_ "b" ("and" @@ "b" @@@ TermFalse ) -:- TermBool ~> TermBool

    section_ "Built-in primitive"

    define_ "and#"
        $$ TermBool ~> TermBool ~> TermBool
        $$ lams_ ["x", "y"] (Inf (TermAnd "x" "y"))

    example_ "and#"
    example_ $ "and#" @@@ TermTrue  @@@ TermTrue
    example_ $ "and#" @@@ TermTrue  @@@ TermFalse
    example_ $ "and#" @@@ TermFalse @@@ TermTrue
    example_ $ "and#" @@@ TermFalse @@@ TermFalse

    subsection_ "Partial evaluation"

    comment_ "With primitive and we get more aggressive reduction behaviour"
    example_ $ lam_ "b" ("and#" @@@ TermTrue @@ "b")  -:- TermBool ~> TermBool
    example_ $ lam_ "b" ("and#" @@@ TermFalse @@ "b") -:- TermBool ~> TermBool
    example_ $ lam_ "b" ("and#" @@ "b" @@@ TermTrue)   -:- TermBool ~> TermBool
    example_ $ lam_ "b" ("and#" @@ "b" @@@ TermFalse ) -:- TermBool ~> TermBool

    comment_ "In fact, literal cannot be in evaluated and-expression:"
    let (/\) :: TermInf s Sym -> TermInf s Sym -> TermInf s Sym
        x /\ y = "and#" @@ Inf x @@ Inf y

    example_ $ lams_ ["x", "y", "z"]
        (Inf $ ("x" /\ TermTrue) /\ ("y" /\ TermTrue /\ "z"))
        -:- TermBool ~> TermBool ~> TermBool ~> TermBool

    example_ $ lams_ ["x", "y", "z"]
        (Inf $ ("x" /\ TermFalse) /\ ("y" /\ TermTrue /\ "z"))
        -:- TermBool ~> TermBool ~> TermBool ~> TermBool

{-
    section_ "Partial application"
    comment_ "Different from partial /evaluation/"

    example_ $ "and" @@@ TermTrue
    example_ $ "and" @@@ TermFalse
    example_ $ lam_ "b" ("and" @@ "b") -:- TermBool ~> TermBool ~> TermBool
    example_ $ "and#" @@@ TermTrue
    example_ $ "and#" @@@ TermFalse
    example_ $ lam_ "b" ("and#" @@ "b") -:- TermBool ~> TermBool ~> TermBool
-}

#endif
#endif
-- $setup
-- >>> :seti -XOverloadedStrings -XTypeApplications
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Systems
