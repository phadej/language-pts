{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.PTS.Examples.Hurkens (
    hurkensScript,
    defineU,
    ) where

import Data.String  (IsString)
import Language.PTS

-- | /A Simplification of Girard's Paradox/ by Hurkens (TLCA '95)
--
-- Hurkens' version fails in HOL, there are no (△,□,□)-rule:
--
-- >>> runSilent $ spec_ HOLStar >> hurkensScript
-- λ» :define ⊥ : ⋆ = ∀ x → x
-- λ» :define ¬ : ⋆ → ⋆ = λ P → P → ⊥
-- λ» :define U : □ = ∏ (X : □) → (((X → ⋆)..
-- error:
-- • No PTS Rule (△,□,-)
-- • when checking expression
--   ∏ (X : □) → (((X → ⋆) → ⋆) → X) → (X → ⋆) → ⋆
--
-- It fails even sooner in predicative systems, because we cannot define ⊥
-- purely; to begin with:
--
-- >>> runSilent $ spec_ (MartinLof 0) >> hurkensScript
-- λ» :define ⊥ : 𝓤 = ∀ x → x
-- error:
-- • Couldn't match expected type 𝓤 with actual type 𝓤₁
-- • In the expression: ∀ x → x
--
-- ...or if we try to define @U@, it will be in the wrong universe:
--
-- >>> runSilent $ spec_ (MartinLof 0) >> defineU
-- λ» :define U : 𝓤₁ = ∏ (X : 𝓤₁) → (((X → 𝓤)..
-- error:
-- • Couldn't match expected type 𝓤₁ with actual type 𝓤₂
-- • In the expression: ∏ (X : 𝓤₁) → (((X → 𝓤) → 𝓤) → X) → (X → 𝓤) → 𝓤
--
-- __However__ in System U, the script goes through:
--
-- >>> runSilent $ spec_ SysUStar >> hurkensScript
-- λ» :define ⊥ : ⋆ = ∀ x → x
-- λ» :define ¬ : ⋆ → ⋆ = λ P → P → ⊥
-- λ» :define U : □ = ∏ (X : □) → (((X → ⋆)..
-- λ» :define Δ : U → ⋆ = λ y → ¬ (∏ (p : (U →..
-- λ» :define Ω : U = λ X f p → (λ p₁ → ∏ (x..
-- λ» :define Θ : ⋆ = ∏ (p : (U → ⋆)) → (∏..
-- λ» :define D : ⋆ = ∏ (p : (U → ⋆)) → Ω U..
-- λ» :define lemma : Θ = λ p t₁ → t₁ Ω (λ x →..
-- λ» :define H : D = λ p → lemma (λ y → p..
-- λ» :define negH : ¬ D = lemma Δ (λ x H₂ H₃ →..
-- λ» :define ¡Ay, caramba! : ⊥ = negH H
-- ∎
--
hurkensScript :: forall s m. Script s m => m ()
hurkensScript = do
    -- Unicode cheating
    let bot, neg, delta, omega, theta :: IsString a => a
        bot = "⊥"
        neg = "¬"
        delta = "Δ"
        omega = "Ω"
        theta = "Θ"

    let tstar, tbox :: CanSort u => u s a
        tstar = sort_ typeSort
        tbox  = sort_ typeSortSort

    section_ "Falsehood and negation"

    define_ bot
        $$ tstar
        $$ forall_ "x" "x"

    define_ neg
        $$ tstar ~> tstar
        $$ lam_ "P" ("P" ~> bot)

    example_ bot
    example_ neg

    section_ "Power set and paradoxial universe"

    comment_ "we need (△,△,△) to define ℘ S = S → ⋆"
    comment_ "luckily we have Haskell as the meta-language"
    let power :: TermInf s a -> TermInf s a
        power s = s ~> tstar

    define_ "U"
        $$ tbox
        $$ pi_ "X" tbox ((power (power "X") ~> "X") ~> power (power "X"))

    example_   "U"
    example_ $ power "U"
    example_ $ power (power "U")

    section_ "Pseudo-terms"

    comment_ "τ : ℘℘U → U"
    let tau :: TermInf s Sym -> TermInf s Sym
        tau t =
            lams_ ["X", "f", "p"] (t @@ lam_ "x" (Inf $ "p" @@ ("f" @@ ("x" @@ "X" @@ "f"))))
            -:- "U"

    comment_ "σ : U → ℘℘U"
    let sigma :: TermInf s Sym -> TermInf s Sym
        sigma s =
            (Inf $ s @@ "U" @@ lam_ "t" (Inf (tau "t")))
            -:- power (power "U")

    let tauSigma = tau . sigma

    section_ "Normal terms"

    define_ delta
        $$ power "U"
        $$ lam_ "y" (neg @@ pi_ "p" (power "U") (sigma "y" @@ "p" ~> "p" @@@ tauSigma "y"))

    define_ omega
        $$ "U"
        $$ Inf (tau (lam_ "p" (pi_ "x" "U" (sigma "x" @@ "p" ~> "p" @@ "x")) -:- power (power "U")))

    define_ theta
        $$ tstar
        $$ Inf (pi_ "p" (power "U") (pi_ "x" "U" (sigma "x" @@ "p" ~> "p" @@ "x") ~> "p" @@ omega))

    define_ "D"
        $$ tstar
        $$ Inf (pi_ "p" (power "U") (sigma omega @@ "p" ~> "p" @@@ tauSigma omega))

    example_ delta
    example_ omega
    example_ theta
    example_ "D"

    section_ "Lemmas"

    define_ "lemma"
        $$ theta
        $$ lams_ ["p", "t1"] ("t1" @@ omega @@ lam_ "x" (Inf ("t1" @@@ tauSigma "x")))

    define_ "H"
        $$ "D"
        $$ lam_ "p" ("lemma" @@ lam_ "y" ("p" @@@ tauSigma "y"))

    define_ "negH"
        $$ neg @@ "D"
        $$ "lemma" @@ delta @@ lams_ ["x", "H2", "H3"]
            ("H3" @@ delta @@ "H2" @@ lam_ "pp" ("H3" @@ lam_ "y" ("pp" @@@ tauSigma "y")))

    section_ "Falsehood evidence"

    define_ "¡Ay, caramba!" $$ bot $$ "negH" @@ "H"

defineU :: forall s m. Script s m => m ()
defineU = do
    let tstar, tbox :: CanSort u => u s a
        tstar = sort_ typeSort
        tbox  = sort_ typeSortSort

    section_ "Power set and paradoxial universe"

    comment_ "we need (△,△,△) to define ℘ S = S → ⋆"
    comment_ "luckily we have Haskell as the meta-language"
    let power :: TermInf s a -> TermInf s a
        power s = s ~> tstar

    define_ "U"
        $$ tbox
        $$ pi_ "X" tbox ((power (power "X") ~> "X") ~> power (power "X"))

-- $setup
-- >>> :set -XOverloadedStrings -XTypeApplications
-- >>> import Language.PTS
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Systems
