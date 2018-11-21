{-# LANGUAGE OverloadedStrings          #-}
-- | __TBW__ Introduction into examples. And more examples.
module Language.PTS.Examples (
    -- * Modules with examples
    module Language.PTS.Examples.Identity,
    module Language.PTS.Examples.Booleans,
    module Language.PTS.Examples.Errors,
    module Language.PTS.Examples.Hurkens,

    -- * Contexts
    module Language.PTS.Examples.Contexts,

    -- * TODO
    lambdaStarPlus,
    natCtx,
#ifdef LANGUAGE_PTS_HAS_NAT
    natSucc,
    natCtx',
#endif
    ) where

import Language.PTS
import Language.PTS.Systems

import Language.PTS.Examples.Identity
import Language.PTS.Examples.Booleans
import Language.PTS.Examples.Errors
import Language.PTS.Examples.Contexts
import Language.PTS.Examples.Hurkens

-------------------------------------------------------------------------------
-- Type-checking nat
-------------------------------------------------------------------------------

-- | Currently @language-pts@ doesn't allow extending the system.
-- (There are commented out "hardcoded" snippets though).
--
-- Yet, we can add types to the context ('natCtx') and typeCheck the
-- plus function.
--
-- >>> prettyPut $ natCtx @LambdaStar "succ"
-- Nat → Nat
--
-- >>> prettyPut $ natCtx @LambdaStar "natElim"
-- Π (m : (Nat → ⋆)) →
-- m zero →
-- (Π (l : Nat) → m l → m (succ l)) →
-- Π (k : Nat) →
-- m k
--
-- But if we try to evaluate plus, we are stuck:
--
-- >>> demo_ natCtx $ lambdaStarPlus @@ ("succ" @@ "zero") @@ "zero"
-- natElim (λ _ → Nat → Nat)
--         (λ n → n)
--         (λ k rec n → succ (rec n))
--         (succ zero)
--         zero
--     ↪ natElim (λ _ → Nat → Nat)
--               (λ n → n)
--               (λ k rec n → succ (rec n))
--               (succ zero)
--               zero
--     : Nat
--
lambdaStarPlus :: Term LambdaStar
lambdaStarPlus = plus

plus :: Specification s => Term s
plus = "natElim"
    @@ lam_ "_" ("Nat" ~> "Nat")
    @@ lam_ "n" "n"
    @@ lams_ ["k" , "rec", "n"] ("succ" @@ ("rec" @@ "n"))

natCtx :: Specification s => Sym -> Maybe (Value s)
natCtx "Nat"     = Just $ sort_ typeSort
natCtx "zero"    = Just   "Nat"
natCtx "succ"    = Just $ "Nat" ~> "Nat"
natCtx "natElim" = Just natElimType
natCtx _ = Nothing

natElimType :: Specification s => Value s
natElimType = pi_ "m"
    ("Nat" ~> sort_ typeSort)
    (mzero ~> msucc ~> res)
  where
    mzero = "m" @@ "zero"
    msucc = pi_ "l" "Nat" ("m" @@ "l" ~> "m" @@ ("succ" @@ "l"))
    res   = pi_ "k" "Nat" ("m" @@ "k")

#ifdef LANGUAGE_PTS_HAS_NAT

natElimType' :: Specification s => Term s
natElimType' = pi_ "m"
    ("Nat" ~> sort_ typeSort)
    (mzero ~> msucc ~> res)
  where
    mzero = "m" @@ "zero"
    msucc = pi_ "l" "Nat" ("m" @@ "l" ~> "m" @@ ("succ" @@ "l"))
    res   = pi_ "k" "Nat" ("m" @@ "k")

natSucc :: Term LambdaStar
natSucc = let_ natCtx' $ "s" @@ ("s" @@ "z")

natCtx' :: Specification s => [(Sym, Term s)]
natCtx' =
    [ "Nat"  .= TermNat
    , "zero" .= TermNatZ
    , "succ" .= lam_ "n" (fromTermInf $ TermNatS "n") -:- "Nat" ~> "Nat"
    , "natElim" .= lams_ ["a", "z", "s", "n"] (fromTermInf $ TermNatElim "a" "z" "s" "n")
        -:- natElimType'
    -- digits
    , "0"   .= "zero"
    , "1"   .= "succ" @@ "0"
    , "2"   .= "succ" @@ "1"
    -- plus
    , "plus" .= plus
    , "plus2" .= lams_ ["n", "m"] ("natElim"
        @@ lam_ "_" "Nat"
        @@ "m"
        @@ lams_ ["k", "n'"] ("succ" @@ "n'")
        @@ "n"
        )
        -:- "Nat" ~> "Nat" ~> "Nat"
    ]

#endif

-------------------------------------------------------------------------------
-- Doctest
-------------------------------------------------------------------------------

-- $setup
-- >>> :set -XOverloadedStrings -XTypeApplications
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Examples.Contexts
