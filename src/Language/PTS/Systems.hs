{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
-- | Various type systems as PTS.
--
-- This module isn't re-exported by "Language.PTS".
module Language.PTS.Systems (
    -- * Consistent
    STLC (..),
    SystemF (..),
    HindleyMilner (..),
    CoC (..),
    MartinLof (..),
    HOL (..),
    -- * Inconsistent
    LambdaStar (..),
    SystemU (..),
    ) where

import Prelude ()
import Prelude.Compat
import Numeric.Natural (Natural)

import Language.PTS.Specification
import Language.PTS.Pretty

-- | \(\lambda^\star\) system.
--
-- /Inconsistent/.
--
-- \[
-- \mathcal{S} = \star \qquad
-- \mathcal{A} = \star : \star \qquad
-- \mathcal{R} = (\star, \star, \star)
-- \]
--
-- >>> prettyPut $ specificationDoc LambdaStar
-- 𝓢: ⋆
-- 𝓐: ⋆ : ⋆
-- 𝓡: (⋆,⋆,⋆)
--
data LambdaStar = LambdaStar deriving (Eq, Show, Enum, Bounded)

instance PrettyPrec LambdaStar where
    ppp _ _ = "⋆"

instance Specification LambdaStar where
    typeSort     = LambdaStar
    typeSortSort = LambdaStar
    axiom _      = Just LambdaStar
    rule _ _     = Just LambdaStar

-- | Simply typed lambda calculus, \(\lambda^\to\).
--
-- \[
-- \mathcal{S} = \star, \square \qquad
-- \mathcal{A} = \star : \square \qquad
-- \mathcal{R} = (\star, \star, \star)
-- \]
--
-- >>> prettyPut $ specificationDoc STLCStar
-- 𝓢: ⋆, □
-- 𝓐: ⋆ : □
-- 𝓡: (⋆,⋆,⋆)
--
data STLC = STLCStar | STLCBox deriving (Eq, Show, Enum, Bounded)

instance PrettyPrec STLC where
    ppp _ STLCStar = pppChar '⋆'
    ppp _ STLCBox  = pppChar '□'

instance Specification STLC where
    typeSort     = STLCStar
    typeSortSort = STLCBox

    axiom STLCStar = Just STLCBox
    axiom _        = Nothing

    rule STLCStar STLCStar = Just STLCStar
    rule _ _               = Nothing

instance HasBox STLC where box_ = STLCBox

-- | System F, \(\lambda2\).
--
-- \[
-- \mathcal{S} = \star, \square \qquad
-- \mathcal{A} = \star : \square \qquad
-- \mathcal{R} = (\star, \star, \star), (\square, \star, \star)
-- \]
--
-- >>> prettyPut $ specificationDoc SysFStar
-- 𝓢: ⋆, □
-- 𝓐: ⋆ : □
-- 𝓡: (⋆,⋆,⋆), (□,⋆,⋆)
--
data SystemF = SysFStar | SysFBox deriving (Eq, Show, Enum, Bounded)

instance PrettyPrec SystemF where
    ppp _ SysFStar = pppChar '⋆'
    ppp _ SysFBox  = pppChar '□'

instance Specification SystemF where
    typeSort     = SysFStar
    typeSortSort = SysFBox

    axiom SysFStar = Just SysFBox
    axiom _        = Nothing

    rule SysFStar SysFStar = Just SysFStar
    rule SysFBox  SysFStar = Just SysFStar
    rule _ _               = Nothing

instance HasBox SystemF where box_ = SysFBox

-- | Hindley-Milner as PTS.
--
-- 'HindleyMilner' is a /truncated/ 'MartinLof': with only two universes.
--
-- \[
-- \mathcal{S} = M, P \qquad
-- \mathcal{A} = M : P \qquad
-- \mathcal{R} = (M,M,M), (P,M,P), (P,P,P)
-- \]
--
-- >>> prettyPut $ specificationDoc HMMono
-- 𝓢: M, P
-- 𝓐: M : P
-- 𝓡: (M,M,M), (P,M,P), (P,P,P)
--
data HindleyMilner = HMMono | HMPoly deriving (Eq, Show, Enum, Bounded)

instance PrettyPrec HindleyMilner where
    ppp _ HMMono = pppChar 'M'
    ppp _ HMPoly = pppChar 'P'

instance Specification HindleyMilner where
    typeSort     = HMMono
    typeSortSort = HMPoly

    axiom HMMono = Just HMPoly
    axiom _      = Nothing

    rule HMMono HMMono = Just HMMono
    rule HMPoly HMMono = Just HMPoly
    rule HMPoly HMPoly = Just HMPoly
    rule _ _           = Nothing

instance HasBox HindleyMilner where box_ = HMPoly

-- | Calculus of Constructions, \(\lambda C\).
--
-- \[
-- \mathcal{S} = \star, \square \qquad
-- \mathcal{A} = \star : \square \qquad
-- \mathcal{R} = (\star, \star, \star), (\square, \star, \star),
--               (\star, \square, \square), (\square, \square, \square)
-- \]
--
-- >>> prettyPut $ specificationDoc CoCStar
-- 𝓢: ⋆, □
-- 𝓐: ⋆ : □
-- 𝓡: (⋆,⋆,⋆), (⋆,□,□), (□,⋆,⋆), (□,□,□)
--
data CoC = CoCStar | CoCBox deriving (Eq, Show, Enum, Bounded)

instance PrettyPrec CoC where
    ppp _ CoCStar = pppChar '⋆'
    ppp _ CoCBox  = pppChar '□'

instance Specification CoC where
    typeSort     = CoCStar
    typeSortSort = CoCBox

    axiom CoCStar = Just CoCBox
    axiom _       = Nothing

    -- full PTS
    rule _ = Just

instance HasBox CoC where box_ = CoCBox

-- | Martin-Löf type system.
--
-- \[
-- \mathcal{S} = \mathbb{N} \qquad
-- \mathcal{A} = n : n + 1; n \in \mathbb{N} \qquad
-- \mathcal{R} = (n, m, \max n\, m); n, m \in \mathbb{N}
-- \]
--
-- >>> prettyPut $ specificationDoc (star_ :: MartinLof)
-- 𝓢: 𝓤, 𝓤1, 𝓤2
-- 𝓐: 𝓤 : 𝓤1, 𝓤1 : 𝓤2, 𝓤2 : 𝓤3
-- 𝓡: (𝓤,𝓤,𝓤),
--    (𝓤,𝓤1,𝓤1),
--    (𝓤1,𝓤,𝓤1),
--    (𝓤1,𝓤1,𝓤1),
--    (𝓤,𝓤2,𝓤2),
--    (𝓤2,𝓤,𝓤2),
--    (𝓤1,𝓤2,𝓤2),
--    (𝓤,𝓤3,𝓤3),
--    (𝓤3,𝓤,𝓤3), ...
--
newtype MartinLof = MartinLof Natural deriving (Eq, Show, Enum)

instance PrettyPrec MartinLof where
    ppp _ (MartinLof 0) = "𝓤"
    ppp _ (MartinLof n) = "𝓤" <> pppIntegral n

instance Specification MartinLof where
    typeSort     = MartinLof 0
    typeSortSort = MartinLof 1

    axiom (MartinLof n) = Just (MartinLof (succ n))

    rule (MartinLof n) (MartinLof m) = Just (MartinLof (max n m))

instance HasBox      MartinLof where box_      = MartinLof 1
instance HasTriangle MartinLof where triangle_ = MartinLof 2

-- | λHOL
--
-- \[
-- \begin{align}
-- \mathcal{S} &= \star, \square, \triangle \newline
-- \mathcal{A} &= \star : \square, \square : \triangle \newline
-- \mathcal{R} &= (\star, \star, \star),
-- (\square, \star, \star), (\square, \square, \square),
-- (\triangle, \star, \star)
-- \end{align}
-- \]
--
-- The $(\triangle, \star, \star)$ is an extension rule.
--
-- >>> prettyPut $ specificationDoc HOLStar
-- 𝓢: ⋆, □, △
-- 𝓐: ⋆ : □, □ : △
-- 𝓡: (⋆,⋆,⋆), (□,⋆,⋆), (□,□,□), (△,⋆,⋆)
--
data HOL = HOLStar | HOLBox | HOLTri deriving (Eq, Show, Enum, Bounded)

instance PrettyPrec HOL where
    ppp _ HOLStar = pppChar '⋆'
    ppp _ HOLBox  = pppChar '□'
    ppp _ HOLTri  = pppChar '△'

instance Specification HOL where
    typeSort     = HOLStar
    typeSortSort = HOLBox

    axiom HOLStar = Just HOLBox
    axiom HOLBox  = Just HOLTri
    axiom _        = Nothing

    rule HOLStar HOLStar = Just HOLStar
    rule HOLBox  HOLStar = Just HOLStar
    rule HOLTri  HOLStar = Just HOLStar -- extension! not in the original HOL
    rule HOLBox  HOLBox  = Just HOLBox
    rule _       _       = Nothing

instance HasBox      HOL where box_      = HOLBox
instance HasTriangle HOL where triangle_ = HOLTri

-- | System U, \(\lambda U\).
--
-- /Inconsistent/.
--
-- \[
-- \begin{align}
-- \mathcal{S} &= \star, \square, \triangle \newline
-- \mathcal{A} &= \star : \square, \square : \triangle \newline
-- \mathcal{R} &= (\star, \star, \star),
-- (\square, \star, \star), (\square, \square, \square),
-- (\triangle, \star, \star), (\triangle, \square, \square)
-- \end{align}
-- \]
--
-- >>> prettyPut $ specificationDoc SysUStar
-- 𝓢: ⋆, □, △
-- 𝓐: ⋆ : □, □ : △
-- 𝓡: (⋆,⋆,⋆), (□,⋆,⋆), (□,□,□), (△,⋆,⋆), (△,□,□)
--
data SystemU = SysUStar | SysUBox | SysUTri deriving (Eq, Show, Enum, Bounded)

instance PrettyPrec SystemU where
    ppp _ SysUStar = pppChar '⋆'
    ppp _ SysUBox  = pppChar '□'
    ppp _ SysUTri  = pppChar '△'

instance Specification SystemU where
    typeSort     = SysUStar
    typeSortSort = SysUBox

    axiom SysUStar = Just SysUBox
    axiom SysUBox  = Just SysUTri
    axiom _        = Nothing

    rule SysUStar SysUStar = Just SysUStar
    rule SysUBox  SysUStar = Just SysUStar
    rule SysUBox  SysUBox  = Just SysUBox
    rule SysUTri  SysUStar = Just SysUStar
    rule SysUTri  SysUBox  = Just SysUBox
    rule _ _               = Nothing

instance HasBox      SystemU where box_      = SysUBox
instance HasTriangle SystemU where triangle_ = SysUTri
