#ifdef LANGUAGE_PTS_HAS_FIXED_POINT
#ifdef LANGUAGE_PTS_HAS_NAT
#ifdef LANGUAGE_PTS_HAS_BOOL
#ifdef LANGUAGE_PTS_HAS_SIGMA
#ifdef LANGUAGE_PTS_HAS_PROP
#ifdef LANGUAGE_PTS_HAS_QUARKS
#define FIXEDPOINT_EXAMPLES
{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
#endif
#endif
#endif
#endif
#endif
#endif
module Language.PTS.Examples.FixedPoint (
#ifdef FIXEDPOINT_EXAMPLES
    fixedPointScript,
#endif
) where

#ifdef FIXEDPOINT_EXAMPLES
import Language.PTS
import Language.PTS.Bound

-- |
--
-- >>> runLoud $ spec_ LambdaStar >> fixedPointScript
--
fixedPointScript :: forall s m. Script s m => m ()
fixedPointScript = do
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

    section_ "Maybe"
    
    define_ "Maybe"
        $$ sort_ typeSort ~> sort_ typeSort
        $$ lams_ ["A"] (Inf $ Sigma "t" TermBool $ abstract1HSym "x" $ "if1" @@ sort_ typeSort @@ "x" @@ "A" @@ Inf Unit)

    subsection_ "Constructors"

    define_ "nothing"
        $$ foralls_ ["A"] ("Maybe" @@ "A")
        $$ lams_ ["A"] (Pair (Inf TermFalse) (Inf I))

    define_ "just"
        $$ foralls_ ["A"] ("A" ~> "Maybe" @@ "A")
        $$ lams_ ["A","x"] (Pair (Inf TermTrue) "x")

    subsection_ "Eliminator"

    let maybeBody :: TermInf s Sym
        maybeBody = TermBoolElim
            "t" (abstract1HSym "t" $ "if1" @@ sort_ typeSort @@ "t" @@ "A" @@ Inf Unit ~> "R")
            (lam_ "x" $ "j" @@ "x")
            (lam_ "y" $ "n")
            "t"

    define_ "maybe"
        $$ foralls_ ["A","R"] ("R" ~> ("A" ~> "R") ~> "Maybe" @@ "A" ~> "R")
        $$ lams_ ["A","R","n","j","m"]
            (Match "m" "t" "v" $ abstract2HSym "t" "v" $ maybeBody @@ "v")

    section_ "Builtin natural numbers"

    define_ "su"
        $$ TermNat ~> TermNat
        $$ lam_ "n" (Inf $ TermNatS "n")

    defineInf_ "ze"
        $$ TermNatZ

    example_ $ "su" @@ ("su" @@ "ze")

    section_ "Natural number as fixed point of Maybe"

    define_ "Nat"
        $$ sort_ typeSort
        $$ Inf (Mu "A" (sort_ typeSort) $ abstract1HSym "A" $ "Maybe" @@ "A")

    define_ "zeroNat"
        $$ "Nat"
        $$ Wrap ("nothing" @@ "Nat")

    define_ "succNat"
        $$ "Nat" ~> "Nat"
        $$ lams_ ["n"] (Wrap $ "just" @@ "Nat" @@ "n")

    define_ "threeNat"
        $$ "Nat"
        $$ "succNat" @@ ("succNat" @@ ("succNat" @@ "zeroNat"))

    example_ "threeNat"

    define_ "toNat"
        $$ "Nat" ~> TermNat
        $$ lams_ ["n"] (Cata "f" "n" $ abstract1HSym "f" $ "maybe" @@ Inf TermNat @@ Inf TermNat @@ "ze" @@ "su" @@ "f")

    example_ $ "toNat" @@ "threeNat"

-- $setup
-- >>> :seti -XOverloadedStrings -XTypeApplications
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Systems
#endif
