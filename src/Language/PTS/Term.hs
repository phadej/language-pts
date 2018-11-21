{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Language.PTS.Term (
    Term,
    TermInf (..),
    TermChk (..),
    TermScope,
    ) where

import Control.Monad        (ap)
import Data.Functor.Classes
import Data.String          (IsString (..))
import Text.Show.Extras

import Language.PTS.Bound
import Language.PTS.Pretty
import Language.PTS.Specification
import Language.PTS.Sym

#ifdef LANGUAGE_PTS_HAS_NAT
import Numeric.Natural
#endif

-------------------------------------------------------------------------------
-- Terms
-------------------------------------------------------------------------------

-- * Terms

type Term s = TermInf s Sym

type TermScope s = ScopeH IrrSym (TermChk s) (TermInf s)

-- | Inferable terms, \(\mathit{Term}_\Rightarrow\).
--
--
data TermInf s a
    = Var a
      -- ^ variable
      --
      -- \[ \frac
      -- {\Gamma (x) = \tau}
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}x \Rightarrow \color{darkred}\tau}
      -- \;\mathrm{V{\scriptstyle AR}}
      -- \]
    | Ann (TermChk s a) (TermInf s a)
      -- ^ annotated term
      --
      -- \[\frac
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}\rho       \Leftarrow \color{darkred}{\sigma} \qquad \rho \leadsto \tau}
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{x : \rho} \Rightarrow \color{darkred}\tau }
      -- \;\mathrm{A{\scriptstyle NN}}
      -- \]
    | Pi  IrrSym (TermInf s a) (ScopeH IrrSym (TermInf s) (TermInf s) a)
      -- ^ dependent function space
      --
      -- \[\frac
      -- {(s,s',s'') \in \mathcal{R} \qquad
      --  \color{darkblue}\Gamma \vdash \color{darkgreen}{\rho} \Leftarrow \color{darkred}s \qquad
      --  \rho \leadsto \tau \qquad
      --  \color{darkblue}{\Gamma, x : \tau} \vdash \color{darkgreen}{\rho'} \Leftarrow \color{darkred}{s'}
      -- }
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\Pi x : \rho.\rho'} \Rightarrow \color{darkred}{s''} }
      -- \;\mathrm{P{\scriptstyle I}}
      -- \]
    | App (TermInf s a) (TermChk s a)
      -- ^ application
      --
      -- \[\frac
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{e}  \Rightarrow \color{darkred}{\Pi x : \tau. \tau'} \qquad
      --  \color{darkblue}\Gamma \vdash \color{darkgreen}{e'} \Leftarrow  \color{darkred}\tau \qquad
      --  \tau'[x \mapsto e'] \leadsto \tau''
      -- }
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{e\, e'} \Rightarrow \color{darkred}{\tau''} }
      -- \;\mathrm{A{\scriptstyle PP}}
      -- \]
    | Sort s
      -- ^ sort
      --
      -- \[\frac
      -- {s : s' \in \mathcal{A}}
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}s \Rightarrow \color{darkred}{s'} }
      -- \;\mathrm{A{\scriptstyle XIOM}}
      -- \]

#ifdef LANGUAGE_PTS_HAS_BOOL
    | TermBool
      -- ^ Booleans.
      --
      -- We assume they are type. (Or we could parametrise them by sort!)
      --
      -- \[\frac
      -- {\star \in \mathcal{S}}
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathbb{B}} \Rightarrow \color{darkred}\star }
      -- \]

    | TermTrue
      -- ^ True.
      --
      -- \[\frac
      -- {}
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathsf{True}} \Rightarrow \color{darkred}{\mathbb{B}} }
      -- \]

    | TermFalse
      -- ^ False.
      --
      -- \[\frac
      -- {}
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathsf{False}} \Rightarrow \color{darkred}{\mathbb{B}} }
      -- \]

    -- | Boolean elimination.
    --
    -- Here we have to assume the target sort (or parametrise further!).
    --
    -- \[ \frac
      -- {\array{
      --  \color{darkblue}{\Gamma, x : \mathbb{B}} \vdash \color{darkgreen}P \Rightarrow \color{darkred}{s}
      --  \qquad
      --  (\star, s, s') \in \mathcal{R}
      --  \cr
      --  P[x \mapsto \mathsf{True}] \leadsto \tau \qquad
      --  \color{darkblue}\Gamma \vdash \color{darkgreen}t \Leftarrow \color{darkred}{\tau}
      --  \cr
      --  P[x \mapsto \mathsf{False}] \leadsto \tau' \qquad
      --  \color{darkblue}\Gamma \vdash \color{darkgreen}f \Leftarrow \color{darkred}{\tau'}
      --  \cr
      --  \color{darkblue}\Gamma \vdash \color{darkgreen}b \Leftarrow \color{darkred}{\mathbb{B}}
      --  \qquad
      --  P[x \mapsto b] \leadsto \sigma
      -- }}
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathbb{B}\mathsf{-elim}\,x\,P\,t\,f\,b} \Rightarrow \color{darkred}{\sigma} }
    -- \]
    | TermBoolElim IrrSym (Scope IrrSym (TermInf s) a) (TermChk s a) (TermChk s a) (TermChk s a)
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
    | TermNat
      -- ^ Natural numbers.
      --
      -- We assume they are type. (Or we could parametrise them by sort!)
      --
      -- \[\frac
      -- {\star \in \mathcal{S}}
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathbb{N}} \Rightarrow \color{darkred}\star }
      -- \]

    | TermNatZ
      -- ^ Zero.
      --
      -- \[\frac
      -- {}
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathsf{Zero}} \Rightarrow \color{darkred}{\mathbb{N}} }
      -- \]
      --
    | TermNatS (TermChk s a)
      -- ^ Successor
      --
      -- \[\frac
      -- {\color{darkbluw}\Gamma \vdash \color{darkgreen}{n}                \Leftarrow  \color{darkred}{\mathbb{N}} }
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathsf{Succ}\,n} \Rightarrow \color{darkred}{\mathbb{N}} }
      -- \]

    -- | Natural numbers elimination.
    --
    -- Here we have to assume the target sort (or parametrise further!).
    --
    -- \[ \frac
      -- {\array{
      --  \color{darkblue}\Gamma \vdash \color{darkgreen}a \Leftarrow \color{darkred}{\mathbb{N} \to \star}
      --  \cr
      --  a\,\mathsf{Zero} \leadsto \tau \qquad
      --  \color{darkblue}\Gamma \vdash \color{darkgreen}z \Leftarrow \color{darkred}{\tau}
      --  \cr
      --  \Pi m : \mathbb{N}. a\,m \to a\,(\mathsf{Succ}\,m)
      --  \leadsto \tau' \qquad
      --  \color{darkblue}\Gamma \vdash \color{darkgreen}s \Leftarrow \color{darkred}{\tau'}
      --  \cr
      --  \color{darkblue}\Gamma \vdash \color{darkgreen}n \Leftarrow \color{darkred}{\mathbb{N}}
      --  \qquad
      --  a\,n \leadsto \sigma
      -- }}
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathbb{N}\mathsf{-elim}\,a\,z\,s\,n} \Rightarrow \color{darkred}{\sigma} }
    -- \]
    | TermNatElim (TermChk s a) (TermChk s a) (TermChk s a) (TermChk s a)
#endif

  deriving (Functor, Foldable, Traversable)

-- | Checkable terms, \(\mathit{Term}_\Leftarrow\).
--
-- A type of the same kind as 'TermInf' to allow abstracting over them.
data TermChk s a
    = Inf (TermInf s a)
      -- ^ inferrable terms
      --
      -- \[\frac
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}x \Rightarrow \color{darkred}\tau }
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}x \Leftarrow \color{darkred}\tau }
      -- \;\mathrm{C{\scriptstyle HK}}
      -- \]
    | Lam IrrSym (TermScope s a)
      -- ^ lambda abstraction
      --
      -- \[\frac
      -- {\color{darkblue}{\Gamma, x : \tau} \vdash \color{darkgreen}{e} \Leftarrow \color{darkred}{\tau'}}
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\lambda x \to e} \Leftarrow \color{darkred}{\Pi x : \tau. \tau'}}
      -- \;\mathrm{L{\scriptstyle AM}}
      -- \]
  deriving (Functor, Foldable, Traversable)

-------------------------------------------------------------------------------
-- Eq instances
-------------------------------------------------------------------------------

-- TODO

-------------------------------------------------------------------------------
-- Show istances
-------------------------------------------------------------------------------

instance Show s => Show1 (TermChk s) where
    liftShowsPrec sp sl d (Inf x) = showsUnaryWith
        (liftShowsPrec sp sl)
        "Inf" d x
    liftShowsPrec sp sl d (Lam x y) = showsBinaryWith
        showsPrec
        (liftShowsPrec sp sl)
        "Lam" d x y

instance Show s => Show1 (TermInf s) where
    liftShowsPrec sp _ d (Var x) = showsUnaryWith
        sp
        "Var" d x
    liftShowsPrec sp sl d (Ann x y) = showsBinaryWith
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "Ann" d x y
    liftShowsPrec sp sl d (Pi x y z) = showsTernaryWith
        showsPrec
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "Pi" d x y z
    liftShowsPrec sp sl d (App x y) = showsBinaryWith
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "App" d x y
    liftShowsPrec _ _ d (Sort x) = showsUnaryWith
        showsPrec
        "Sort" d x

#ifdef LANGUAGE_PTS_HAS_BOOL
    liftShowsPrec _  _  _ TermBool                 = showString "TermBool"
    liftShowsPrec _  _  _ TermTrue                 = showString "TermTrue"
    liftShowsPrec _  _  _ TermFalse                = showString "TermFalse"
    liftShowsPrec sp sl d (TermBoolElim x y z w u) = showsQuintWith
        showsPrec
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "TermBoolElim" d x y z w u
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
    liftShowsPrec _  _  _ TermNat      = showString "TermNat"
    liftShowsPrec _  _  _ TermNatZ     = showString "TermNatZ"
    liftShowsPrec sp sl d (TermNatS x) = showsUnaryWith
        (liftShowsPrec sp sl)
        "TermNatS" d x
    liftShowsPrec sp sl d (TermNatElim x y z w) = showsQuadWith
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "TermNatElim" d x y z w
#endif

instance (Show a, Show s) => Show (TermInf s a) where showsPrec = showsPrec1
instance (Show a, Show s) => Show (TermChk s a) where showsPrec = showsPrec1

-------------------------------------------------------------------------------
-- PrettyPrec
-------------------------------------------------------------------------------

instance Specification s => PrettyPrec1 (TermInf s) where
    liftPpp p d t = traverse (p PrecApp) t >>= pppInf d

pppInf :: Specification s => Prec -> TermInf s Doc -> PrettyM Doc
pppInf _ (Var a)     = return a
pppInf d (Sort s)    = ppp d s
pppInf d t@Pi {}     = uncurry (pppPi d) =<< pppPeelPi t
pppInf d t@App {}    = uncurry (pppApplication d) (pppPeelApplication t)
pppInf d (Ann x t'@Pi {}) =
    uncurry (pppAnnotationPi d (pppChk PrecAnn x)) =<< pppPeelPi t'
pppInf d (Ann x t)   = pppAnnotation d (pppChk PrecAnn x) (pppInf PrecAnn t)

#ifdef LANGUAGE_PTS_HAS_BOOL
pppInf _ TermBool    = pppChar '𝔹'
pppInf _ TermTrue    = pppText "true"
pppInf _ TermFalse   = pppText "false"
pppInf d (TermBoolElim x p t f b) = pppApplication d
        (pppText "𝔹-elim")
        [ pppScopedIrrSym x $ \xDoc -> pppLambda PrecApp [xDoc] $ pppInf PrecLambda $ instantiate1return xDoc p
        , pppChk PrecApp t
        , pppChk PrecApp f
        , pppChk PrecApp b
        ]
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
pppInf _ TermNat      = pppChar 'ℕ'
pppInf _ TermNatZ     = pppChar '0'
pppInf d (TermNatS n)
    | Just m <- termChkToNatural n = pppIntegral m
    | otherwise                    = pppApplication d (pppChar 'S') [pppChk PrecApp n]
pppInf d (TermNatElim a z s n) = pppApplication d
        (pppText "ℕ-elim")
        [ pppChk PrecApp a
        , pppChk PrecApp z
        , pppChk PrecApp s
        , pppChk PrecApp n
        ]
#endif

pppPeelPi :: Specification s => TermInf s Doc -> PrettyM ([PPPi], PrettyM Doc)
pppPeelPi (Pi n a b)
    | Just b' <- unusedScopeH b = do
        ~(xs, ys) <- pppPeelPi b'
        return (PPArrow (pppInf PrecPi a) : xs, ys)
    | Sort a' <- a, a' == typeSort =
        pppScopedIrrSym n $ \nDoc -> do
            ~(xs, ys) <- pppPeelPi (instantiate1H (return nDoc) b)
            return (PPForall nDoc : xs, ys)
    | otherwise =
        pppScopedIrrSym n $ \nDoc -> do
            ~(xs, ys) <- pppPeelPi (instantiate1H (return nDoc) b)
            return (PPPi nDoc (pppInf PrecPi a) : xs, ys)

pppPeelPi t = return ([], pppInf PrecPi t)

pppPeelApplication :: Specification s => TermInf s Doc -> (PrettyM Doc, [PrettyM Doc])
pppPeelApplication (App f x) =
    let ~(f', xs) = pppPeelApplication f
    in (f', xs ++ [pppChk PrecApp x])
pppPeelApplication t = (pppInf PrecApp t, [])

unusedScopeH :: (Module f g, Traversable f) => ScopeH n f g a -> Maybe (f a)
unusedScopeH s = sequence (instantiate1H (return Nothing) (fmap Just s))

instance Specification s => PrettyPrec1 (TermChk s) where
    liftPpp p d t = traverse (p PrecApp) t >>= pppChk d

pppChk :: forall s. Specification s => Prec -> TermChk s Doc -> PrettyM Doc
pppChk d (Inf x)  = pppInf d x
pppChk d t@Lam {} = uncurry (pppLambda d) =<< pppPeelLam t
  where
    pppPeelLam :: TermChk s Doc -> PrettyM ([Doc], PrettyM Doc)
    pppPeelLam (Inf x)   = do
        x' <- pppInf PrecLambda x
        return ([], return x')
    pppPeelLam (Lam n b) = pppScopedIrrSym n $ \nDoc -> do
        ~(xs, ys) <- pppPeelLam (instantiate1H (return nDoc) b)
        return (nDoc : xs, ys)

instance (Specification s, PrettyPrec a) => PrettyPrec (TermInf s a) where ppp = ppp1
instance (Specification s, PrettyPrec a) => PrettyPrec (TermChk s a)  where ppp = ppp1

-------------------------------------------------------------------------------
-- Monad instances
-------------------------------------------------------------------------------

instance Applicative (TermInf s) where
    pure  = Var
    (<*>) = ap

instance Monad (TermInf s) where
    return = pure

    Var a    >>= f = f a
    Ann x t  >>= f = Ann (x >>== f) (t >>= f)
    Sort s   >>= _ = Sort s
    App u d  >>= f = App (u >>= f) (d >>== f)
    Pi n a b >>= f = Pi n (a >>= f) (b >>== f)

#ifdef LANGUAGE_PTS_HAS_BOOL
    TermBool               >>= _ = TermBool
    TermTrue               >>= _ = TermTrue
    TermFalse              >>= _ = TermFalse
    TermBoolElim x p z s n >>= k = TermBoolElim x
        (p >>>= k)
        (z >>== k)
        (s >>== k)
        (n >>== k)
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
    TermNat             >>= _ = TermNat
    TermNatZ            >>= _ = TermNatZ
    TermNatS n          >>= k = TermNatS (n >>== k)
    TermNatElim a z s n >>= k = TermNatElim
        (a >>== k)
        (z >>== k)
        (s >>== k)
        (n >>== k)
#endif

instance Module (TermChk s) (TermInf s) where
    Inf u   >>== k = Inf (u >>= k)
    Lam n b >>== k = Lam n (b >>== k)

instance Module (TermInf s) (TermInf s) where
    (>>==) = (>>=)

-------------------------------------------------------------------------------
-- Extension extra
-------------------------------------------------------------------------------

#ifdef LANGUAGE_PTS_HAS_NAT
termChkToNatural :: TermChk s a -> Maybe Natural
termChkToNatural (Inf TermNatZ)     = Just 0
termChkToNatural (Inf (TermNatS n)) = succ <$> termChkToNatural n
termChkToNatural _                  = Nothing
#endif

-------------------------------------------------------------------------------
-- Smart constructors
-------------------------------------------------------------------------------

instance IsString a => IsString (TermInf s a) where
    fromString = Var . fromString

instance IsString a => IsString (TermChk s a) where
    fromString = Inf . fromString
