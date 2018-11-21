{-# LANGUAGE OverloadedStrings #-}
module Language.PTS.Examples.Booleans (
    churchBooleansScript,
#if defined(LANGUAGE_PTS_HAS_BOOL) && defined(LANGUAGE_PTS_HAS_NAT)
    booleansScript,
#endif
    ) where

import Language.PTS

#if defined(LANGUAGE_PTS_HAS_BOOL) && defined(LANGUAGE_PTS_HAS_NAT)
import Control.Monad.Trans.Class (lift)

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
              (Inf $ TermBoolElim "_" (lift "r") "t" "f" "b")

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

    let ty = TermBoolElim "_" (lift $ sort_ typeSort) (Inf TermBool) (Inf TermNat) "b"
    define_ "contrived"
        $$ pi_ "b" TermBool
              (TermBoolElim "_" (lift $ sort_ typeSort) (Inf TermBool) (Inf TermNat) "b")
        $$ lam_ "b"
            (Inf $ TermBoolElim "p" (abstract1Sym "b" ty) (Inf TermTrue) (Inf TermNatZ)  "b")

    example_ "contrived"
    example_ $ "contrived" @@@ TermTrue
    example_ $ "contrived" @@@ TermFalse
#endif

-- $setup
-- >>> :seti -XOverloadedStrings -XTypeApplications
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Systems
