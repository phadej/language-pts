module Language.PTS.Specification (
    -- * PTS Specifications
    Specification (..),
    ReflectiveSpecification (..),
    specificationDoc,
    -- * Individual universes.
    star_,
    HasBox (..),
    HasTriangle (..),
    ) where

import Prelude ()
import Prelude.Compat
import Data.Foldable (toList)

import Language.PTS.Pretty


-- | Specification of a Pure Type System.
--
-- Laws
--
-- @
-- 'axiom' 'typeSort' = Just 'typeSortSort'
-- @
--
-- By requiring \(\mathcal{A} \subset \mathcal{S}\times\mathcal{S}\)
-- and \(\mathcal{R} \subset (\mathcal{S}\times\mathcal{S})\times\mathcal{R}\)
-- to be functions, we get uniqueness of types in PTS. (And let's us make
-- bi-directional type-system).
--
class (Eq s, Show s, Enum s, PrettyPrec s) => Specification s where
    -- | Sort of types. Usually \(\star\).
    --
    -- \[
    -- \mathit{True} : \mathit{Bool} : \star
    -- \]
    typeSort :: s

    -- | Sort of sort of types.
    --
    -- In lambda cube systems we have \(\star : \square\);
    -- in \(\lambda^\star\) we have \(\star : \star\).
    --
    -- Note that in STLC, \(\lambda^\to\) we don't have
    -- \((\square, \star, -) \in \mathcal{R}\)
    -- so we cannot have 'forAll', \(\forall\).
    typeSortSort :: s

    -- | Some sorts have a types. \(\mathcal{A}\).
    --
    -- @Just s2 = 'axiom' s1@ induces a typing rule
    --
    -- \[
    -- \frac{}{
    -- \Gamma \vdash s_1 \Rightarrow s_2
    -- }\;\mathsf{Axiom}
    -- \]
    axiom :: s -> Maybe s

    -- | Rules for products. \(\mathcal{R}\).
    --
    -- @Just s3 = 'rule' s1 s2@ induces a typing rule
    --
    -- \[
    -- \frac{
    -- \Gamma \vdash \alpha \Leftarrow s_1
    -- \qquad
    -- \alpha \Downarrow \alpha'
    -- \qquad
    -- \Gamma,x:\alpha' \vdash \beta \Leftarrow s_2
    -- }{
    -- \Gamma \vdash \forall x : \alpha.\beta \Rightarrow s_3
    -- }\;\mathsf{Pi}
    -- \]
    rule :: s -> s -> Maybe s

class Specification s => ReflectiveSpecification s where
    axiom' :: s -> s

    relationSort :: s -> s

-- | Pretty-print specification
--
specificationDoc :: Specification s => s -> PrettyM Doc
specificationDoc s =
    pppText "𝓢:" <+> pppHsepPunctuated pppComma_
        [ ppp0 x | x <- take 3 [ s.. ] ]
    $$$
    pppText "𝓐:" <+> pppHsepPunctuated pppComma_
        [ ppp0 x <+> pppColon <+> ppp0 y
        | x <- take 3 [ s.. ]
        , y <- toList (axiom x)
        ]
    $$$
    pppText "𝓡:"
        <+> pppSepPunctuated pppComma_ pppRules
        <> (if more then pppText ", ..." else mempty)
  where
    pppRules =
        [ pppParens True $ pppCatPunctuated pppComma_ $ map (ppp0) [x, y, z]
        | (x, y, z) <- take 9 rules
        ]

    rules =
        [ (x,y,z)
        | (y, x) <- fair [s ..] [s ..]
        , z <- toList (rule x y)
        ]
    more = not (null (drop 9 rules))
    

-- | "fair" interleaving
--
-- >>> fair [1..4] [1..4]
-- [(1,1),(2,1),(1,2),(2,2),(3,1),(1,3),(3,2),(4,1),(1,4),(2,3),(3,3),(4,2),(2,4),(4,3),(3,4),(4,4)]
fair :: [a] -> [b] -> [(a, b)]
fair [] _              = []
fair _  []             = []
fair (x : xs) (y : ys) = (x,y) : inter3
    (map (\x' -> (x',y)) xs)
    (map (\y' -> (x,y')) ys)
    (fair xs ys)

inter3 :: [c] -> [c] -> [c] -> [c]
inter3 []     ys     zs     = inter2 ys zs
inter3 xs     []     zs     = inter2 xs zs
inter3 xs     ys     []     = inter2 xs ys
inter3 (x:xs) (y:ys) (z:zs) = x : y : z : inter3 xs ys zs

inter2 :: [c] -> [c] -> [c]
inter2 []     ys     = ys
inter2 xs     []     = xs
inter2 (x:xs) (y:ys) = x : y : inter2 xs ys

star_ :: Specification s => s
star_ = typeSort

class Specification s => HasBox s where
    box_ :: s

class HasBox s => HasTriangle s where
    triangle_ :: s 
