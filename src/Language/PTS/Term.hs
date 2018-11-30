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
    ScopeInf,
    ScopeChkInf,
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

#ifdef LANGUAGE_PTS_HAS_QUARKS
import Data.Set (Set)
import Data.Map (Map)

import qualified Data.Set as Set
import qualified Data.Map as Map
#endif

-------------------------------------------------------------------------------
-- Terms
-------------------------------------------------------------------------------

-- * Terms

type Term s = TermInf s Sym

type ScopeInf n s a = ScopeH n (TermInf s) (TermInf s) a
type ScopeChkInf n s a = ScopeH n (TermChk s) (TermInf s) a

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
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\rho} \Rightarrow \color{darkred}s
      --  \qquad
      --  \rho \leadsto \tau
      --  \qquad
      --  \color{darkblue}{\Gamma, x : \tau} \vdash \color{darkgreen}{\rho'} \Rightarrow \color{darkred}{s'}
      --  \qquad
      --  (s,s',s'') \in \mathcal{R}
      -- }
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\prod (x : \rho) \to \rho'} \Rightarrow \color{darkred}{s''} }
      -- \;\mathsf{Pi}
      -- \]
    | App (TermInf s a) (TermChk s a)
      -- ^ application
      --
      -- \[\frac
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{e}  \Rightarrow \color{darkred}{\prod (x : \tau) \to \tau'} \qquad
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

#ifdef LANGUAGE_PTS_HAS_SIGMA
      -- | Dependent pair
      --
      -- \[\frac
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\rho} \Rightarrow \color{darkred}s
      --  \qquad
      --  \rho \leadsto \tau
      --  \qquad
      --  \color{darkblue}{\Gamma, x : \tau} \vdash \color{darkgreen}{\rho'} \Rightarrow \color{darkred}{s'}
      --  \qquad
      --  (s,s',s'') \in \mathcal{R}
      -- }
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\sum (x : \rho) \to \rho'} \Rightarrow \color{darkred}{s''} }
      -- \;\mathsf{Sigma}
      -- \]
    | Sigma IrrSym (TermInf s a) (ScopeH IrrSym (TermInf s) (TermInf s) a)
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
      -- | Propositional equality
      --
      -- \[\frac
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\rho} \Rightarrow \color{darkred}{s}
      --  \qquad \rho \leadsto \tau
      --  \qquad \color{darkblue}\Gamma \vdash \color{darkgreen}{x} \Leftarrow \color{darkred}{\tau}
      --  \qquad \color{darkblue}\Gamma \vdash \color{darkgreen}{y} \Leftarrow \color{darkred}{\tau}
      -- }
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathsf{Eq}\;\rho\;x\;y} \Rightarrow \color{darkred}{s} }
      -- \;\mathsf{Eq}
      -- \]
    | Equality (TermInf s a) (TermChk s a) (TermChk s a)


      -- | J-rule. Propositional equality elimination.
      --
      -- \[\frac
      -- {\array{
      -- \color{darkblue}\Gamma \vdash \color{darkgreen}{a} \Rightarrow \color{darkred}{s} \qquad s \in \mathcal{S}
      -- \cr
      -- \color{darkblue}{\Gamma, x : A, y : A, z : \mathsf{Eq}\,a\,x\,y} \vdash \color{darkgreen}{P} \Rightarrow \color{darkred}{s'} \qquad s' \in \mathcal{S}
      -- \cr
      -- \color{darkblue}{\Gamma, q : A} \vdash \color{darkgreen}{r} \Leftarrow \color{darkred}{P [ x \mapsto q; y \mapsto q; z \mapsto \mathsf{refl}]}
      -- \cr
      -- \color{darkblue}{\Gamma} \vdash \color{darkgreen}{u} \Leftarrow \color{darkred}{a}
      -- \qquad
      -- \color{darkblue}{\Gamma} \vdash \color{darkgreen}{v} \Leftarrow \color{darkred}{a}
      -- \qquad
      -- \color{darkblue}{\Gamma} \vdash \color{darkgreen}{w} \Leftarrow \color{darkred}{\mathsf{Eq}\,A\,u\,v}
      -- }}
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathsf{J}\;a\;(\lambda\,x\,y\,z \to c)\;(\lambda\,q \to r)\;u\,v\,w} \Rightarrow \color{darkred}{P [ x \mapsto u; y \mapsto v; z \mapsto w]} }
      -- \;\mathsf{J}
      -- \]
    | J (V3 IrrSym)             -- x y z - symbols
        (TermInf s a)           -- a : s
        (ScopeInf IrrSym3 s a)  -- P : (x y : a) -> (z : Eq a x y) -> s')
        (TermChk s a)           -- r : (q : a) -> P q q (refl a q)
        (TermChk s a)           -- u : a
        (TermChk s a)           -- v : a
        (TermChk s a)           -- w : Eq a u v
                                --   : P u v w
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
    -- | Tautology.
    --
    -- \[\frac
    -- {}
    -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\top} \Rightarrow \color{darkred}\star}
    -- \]
    | Unit

    -- | Tautology witness.
    --
    -- \[\frac
    -- {}
    -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathsf{I}} \Rightarrow \color{darkred}\top}
    -- \]
    | I

    -- | Contradiction.
    --
    -- \[\frac
    -- {}
    -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\bot} \Rightarrow \color{darkred}\star}
    -- \]
    | Empty
#endif

#ifdef LANGUAGE_PTS_HAS_BOOL
    | TermBool
      -- ^ Booleans
      --
      -- \[\frac
      -- {}
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
    -- /Note:/ \(\mathbb{B}\mathsf{-elim}\) is universe-polymorphic.
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
    -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathbb{B}\mathsf{-elim}\,(\lambda\, x \to P) \,t\,f\,b} \Rightarrow \color{darkred}{\sigma} }
    -- \]
    | TermBoolElim IrrSym (ScopeInf IrrSym s a) (TermChk s a) (TermChk s a) (TermChk s a)

#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM

    -- | Boolean conjunction, @and@.
    --
    -- \[ \frac
      -- {\array{
      --  \color{darkblue}\Gamma \vdash \color{darkgreen}x \Leftarrow \color{darkred}{\mathbb{B}}
      --  \qquad
      --  \color{darkblue}\Gamma \vdash \color{darkgreen}y \Leftarrow \color{darkred}{\mathbb{B}}
      -- }}
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathbb{B}\mathsf{-and}\,x\,y} \Rightarrow \color{darkred}{\mathbb{B}} }
    -- \]
    | TermAnd (TermChk s a) (TermChk s a)
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
    | TermNat
      -- ^ Natural numbers.
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
    --  \color{darkblue}{\Gamma, x : \mathbb{N}} \vdash \color{darkgreen}P \Leftarrow \color{darkred}{s}
    --  \qquad
    --  (\star, s, s') \in \mathcal{R}
    --  \cr
    --  P[x \mapsto \mathsf{Zero}] \leadsto \tau \qquad
    --  \color{darkblue}\Gamma \vdash \color{darkgreen}z \Leftarrow \color{darkred}{\tau}
    --  \cr
    --  \prod (l : \mathbb{N}) \to P[x \mapsto l] \to P[x \mapsto \mathsf{Succ}\,l]
    --  \leadsto \tau' \qquad
    --  \color{darkblue}\Gamma \vdash \color{darkgreen}s \Leftarrow \color{darkred}{\tau'}
    --  \cr
    --  \color{darkblue}\Gamma \vdash \color{darkgreen}n \Leftarrow \color{darkred}{\mathbb{N}}
    --  \qquad
    --  P[x \mapsto n] \leadsto \sigma
    -- }}
    -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathbb{N}\mathsf{-elim}\,(\lambda\, x \to p)\,z\,s\,n} \Rightarrow \color{darkred}{\sigma} }
    -- \]
    | TermNatElim IrrSym (ScopeInf IrrSym s a) (TermChk s a) (TermChk s a) (TermChk s a)

#ifdef LANGUAGE_PTS_HAS_NAT_PRIM

    -- | Natural number addition, @plus@.
    --
    -- \[ \frac
      -- {\array{
      --  \color{darkblue}\Gamma \vdash \color{darkgreen}x \Leftarrow \color{darkred}{\mathbb{N}}
      --  \qquad
      --  \color{darkblue}\Gamma \vdash \color{darkgreen}y \Leftarrow \color{darkred}{\mathbb{N}}
      -- }}
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathbb{N}\mathsf{-plus}\,x\,y} \Rightarrow \color{darkred}{\mathbb{N}} }
    -- \]
    | TermPlus (TermChk s a) (TermChk s a)

    -- | Natural number addition, @times@.
    --
    -- \[ \frac
      -- {\array{
      --  \color{darkblue}\Gamma \vdash \color{darkgreen}x \Leftarrow \color{darkred}{\mathbb{N}}
      --  \qquad
      --  \color{darkblue}\Gamma \vdash \color{darkgreen}y \Leftarrow \color{darkred}{\mathbb{N}}
      -- }}
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathbb{N}\mathsf{-times}\,x\,y} \Rightarrow \color{darkred}{\mathbb{N}} }
    -- \]
    | TermTimes (TermChk s a) (TermChk s a)
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
    -- | Hadron type.
    --
    -- In physics, /quarks/ combine to form composite particles called /hadrons/.
    -- In our type system(s) /quark/ combine to form types.
    -- Hadrons are /finite sets/ (enumerations).
    --
    -- We call single quark hadrons /atoms/.
    -- This is not true in physics, but we do get lisp-like atoms this way;
    -- i.e. things which are equal to itself only.
    -- But we agree with modern physics: atoms are not indivisible.
    --
    -- \[\frac
    -- {\star \in \mathcal{S}}
    -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\{\overline{:\!\!q}\}} \Rightarrow \color{darkred}\star }
    -- \]
    | Hadron (Set Sym)


    -- | Quark elimination.
    --
    -- The rule is not the same as in /PiSigma/ label (which influenced quark design).
    -- There the rule is checkable, but we have to provide a motive.
    --
    -- /Note:/ here we infer the type of hadron from the match clauses.
    -- That way we get exhautivity check.
    --
    -- The /real/ reason for the quark name is because \(\mathbb{Q}\) is better supported in fonts, than e.g. \(\mathbb{L}\).
    --
    -- \[ \frac
    -- {\array{
    --  \color{darkblue}{\Gamma, x : \{\overline{:\!\!q}\}} \vdash \color{darkgreen}P \Rightarrow \color{darkred}{s}
    --  \qquad
    --  (\star, s, s') \in \mathcal{R}
    --  \cr
    --  P[x \mapsto :\!\!q_i] \leadsto \tau_i
    --  \qquad
    --  \color{darkblue}\Gamma \vdash \color{darkgreen}{u_i} \Leftarrow \color{darkred}{\tau_i}
    --  \cr
    --  \color{darkblue}\Gamma \vdash \color{darkgreen}t \Leftarrow \color{darkred}{\{\overline{:\!\!q}\}}
    --  \qquad
    --  P[x \mapsto t] \leadsto \sigma
    -- }}
    -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathbb{Q}\mathsf{-elim}\,(\lambda\, x \to P)\;\{\overline{:\!\!q \longrightarrow u}\}\;t} \Rightarrow \color{darkred}{\sigma} }
    -- \]
    | QuarkElim IrrSym (ScopeInf IrrSym s a) (Map Sym (TermChk s a)) (TermChk s a)
#endif

  deriving (Functor, Foldable, Traversable)

-- | Checkable terms, \(\mathit{Term}_\Leftarrow\).
--
-- A type of the same kind as 'TermInf' to allow abstracting over them.
data TermChk s a
      -- | Inferrable terms
      --
      -- \[\frac
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}x \Rightarrow \color{darkred}{\tau'}
      --  \qquad
      --  \tau \equiv \tau'
      -- }
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}x \Leftarrow \color{darkred}\tau }
      -- \;\mathrm{C{\scriptstyle HK}}
      -- \]
    = Inf (TermInf s a)

      -- | Lambda abstraction
      --
      -- \[\frac
      -- {\color{darkblue}{\Gamma, x : \tau} \vdash \color{darkgreen}{e} \Leftarrow \color{darkred}{\tau'}}
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\lambda\, x \to e} \Leftarrow \color{darkred}{\prod (x : \tau) \to \tau'}}
      -- \;\mathrm{L{\scriptstyle AM}}
      -- \]
    | Lam IrrSym (ScopeChkInf IrrSym s a)


#ifdef LANGUAGE_PTS_HAS_SIGMA
      -- | Dependent pair
      --
      -- \[\frac
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{x} \Leftarrow \color{darkred}{\tau}
      -- \qquad
      -- \color{darkblue}\Gamma \vdash \color{darkgreen}{y} \Leftarrow \color{darkred}{\tau' [ x \mapsto \tau} ]
      -- }
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathsf{pair}\;x\;y} \Leftarrow \color{darkred}{\sum (x : \tau) \to \tau'}}
      -- \]
    | Pair (TermChk s a) (TermChk s a)

      -- | Dependent pattern match
      --
      -- @match p (\x y -> b) ~ (\x y -> b) (fst p) (snd p)@
      --
      -- \[\frac
      -- {
      -- \color{darkblue}\Gamma \vdash \color{darkgreen}p \Rightarrow \color{darkred}{\sum (z : \tau) \to \tau'}
      -- \qquad
      -- \color{darkblue}{\Gamma, x : \tau, y : \tau' [z \mapsto x]} \vdash b \Leftarrow \color{darkred}{\tau''}
      -- }
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathsf{match}\;p\;(\lambda\, x\, y \to b)} \Leftarrow \color{darkred}{\tau''}}
      -- \]
    | Match (TermInf s a) IrrSym IrrSym (ScopeChkInf IrrSym2 s a)
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
      -- | Witness or propositional equality
      --
      -- \[\frac
      -- {x \equiv y}
      -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathsf{refl}} \Leftarrow \color{darkred}{\mathsf{Eq}\;\tau\;x\;y}}
      -- \]
    | Refl
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
    -- | Ex falso quodlibet.
    --
    -- \[\frac
    -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{x} \Leftarrow \color{darkred}\bot}
    -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{\mathsf{absurd}\;x} \Leftarrow \color{darkred}{\tau}}
    -- \]
    | Absurd (TermChk s a)
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
    -- | Single quark.
    --
    -- Compare to Booleans: 'TermTrue' and 'TermFalse'.
    -- Here we don't know the type of hadron a quark belongs to, we must check it;
    -- On the other hand, Boolean literals are inferrable.
    --
    -- Quarks are prefixed with a colon, to syntatically distinguish them.
    --
    -- \[\frac
    -- {:\!\!x \in \overline{:\!\!q}}
    -- {\color{darkblue}\Gamma \vdash \color{darkgreen}{:\!\!x} \Leftarrow \color{darkred}{\{\overline{:\!\!q}\}} }
    -- \]

    | Quark Sym
#endif

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

#ifdef LANGUAGE_PTS_HAS_SIGMA
    liftShowsPrec sp sl d (Pair x y) = showsBinaryWith
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "Pair" d x y

    liftShowsPrec sp sl d (Match x y z w) = showsQuadWith
        (liftShowsPrec sp sl)
        showsPrec
        showsPrec
        (liftShowsPrec sp sl)
        "Match" d x y z w
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
    liftShowsPrec _ _ _ Refl = showString "Refl"
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
    liftShowsPrec sp sl d (Absurd x) = showsUnaryWith
        (liftShowsPrec sp sl)
        "Absurd" d x
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
    liftShowsPrec _ _ d (Quark q) = showsUnaryWith
        showsPrec
        "Quark" d q
#endif

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

#ifdef LANGUAGE_PTS_HAS_SIGMA
    liftShowsPrec sp sl d (Sigma x y z) = showsTernaryWith
        showsPrec
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "Sigma" d x y z
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
    liftShowsPrec sp sl d (J v3 a p r u v w) = showParen (d >= 10)
        $ showString "J"
        . showChar ' ' . showsPrec 11 v3
        . showChar ' ' . liftShowsPrec sp sl 11 a
        . showChar ' ' . liftShowsPrec sp sl 11 p
        . showChar ' ' . liftShowsPrec sp sl 11 r
        . showChar ' ' . liftShowsPrec sp sl 11 u
        . showChar ' ' . liftShowsPrec sp sl 11 v
        . showChar ' ' . liftShowsPrec sp sl 11 w
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
    liftShowsPrec sp sl d (Equality x y z) = showsTernaryWith
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "Equality" d x y z
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
    liftShowsPrec _  _  _ Unit  = showString "Unit"
    liftShowsPrec _  _  _ I     = showString "I"
    liftShowsPrec _  _  _ Empty = showString "Empty"
#endif
        
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

#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM
    liftShowsPrec sp sl d (TermAnd x y) = showsBinaryWith
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "TermAnd" d x y
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
    liftShowsPrec _  _  _ TermNat      = showString "TermNat"
    liftShowsPrec _  _  _ TermNatZ     = showString "TermNatZ"
    liftShowsPrec sp sl d (TermNatS x) = showsUnaryWith
        (liftShowsPrec sp sl)
        "TermNatS" d x
    liftShowsPrec sp sl d (TermNatElim x y z w u) = showsQuintWith
        showsPrec
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "TermNatElim" d x y z w u

#ifdef LANGUAGE_PTS_HAS_NAT_PRIM
    liftShowsPrec sp sl d (TermPlus x y) = showsBinaryWith
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "TermPlus" d x y

    liftShowsPrec sp sl d (TermTimes x y) = showsBinaryWith
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "TermTimes" d x y
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
    liftShowsPrec _ _ d (Hadron qs) = showsUnaryWith
        showsPrec
        "Hadron" d (Set.toList qs)

    liftShowsPrec sp sl d (QuarkElim x p qs q) = showsQuadWith
        showsPrec
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        (liftShowsPrec sp sl)
        "QuarkElim" d x p (P $ Map.toList qs) q
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

#ifdef LANGUAGE_PTS_HAS_SIGMA
pppInf d t@Sigma {} = uncurry (pppPi d) =<< pppPeelPi t
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
pppInf d (Equality a x y) = pppApplication d
    "Eq"
    [ pppInf PrecApp a
    , pppChk PrecApp x
    , pppChk PrecApp y
    ]

pppInf d (J (V3 x y z) a p r u v w) = pppApplication d
    (pppText "J")
    [ pppInf PrecApp a
    , pppScopedIrrSym x $ \xDoc ->
      pppScopedIrrSym y $ \yDoc ->
      pppScopedIrrSym z $ \zDoc ->
      pppLambda PrecApp [xDoc,yDoc,zDoc] $ pppInf PrecLambda $ instantiate3Hreturn xDoc yDoc zDoc p
    , pppChk PrecApp r
    , pppChk PrecApp u
    , pppChk PrecApp v
    , pppChk PrecApp w
    ]
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
pppInf _ Unit  = pppChar '⊤'
pppInf _ I     = pppChar 'I'
pppInf _ Empty = pppChar '⊥'
#endif

#ifdef LANGUAGE_PTS_HAS_BOOL
pppInf _ TermBool    = pppChar '𝔹'
pppInf _ TermTrue    = pppText "true"
pppInf _ TermFalse   = pppText "false"
pppInf d (TermBoolElim x p t f b) = pppApplication d
        (pppText "𝔹-elim")
        [ pppScopedIrrSym x $ \xDoc -> pppLambda PrecApp [xDoc] $ pppInf PrecLambda $ instantiate1Hreturn xDoc p
        , pppChk PrecApp t
        , pppChk PrecApp f
        , pppChk PrecApp b
        ]

#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM
pppInf d (TermAnd x y) = pppApplication d
    (pppText "𝔹-and")
    [ pppChk PrecApp x
    , pppChk PrecApp y
    ]
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
pppInf _ TermNat      = pppChar 'ℕ'
pppInf _ TermNatZ     = pppChar '0'
pppInf d (TermNatS n)
    | Just m <- termChkToNatural n = pppIntegral $ succ m
    | otherwise                    = pppApplication d (pppChar 'S') [pppChk PrecApp n]
pppInf d (TermNatElim x p z s n) = pppApplication d
        (pppText "ℕ-elim")
        [ pppScopedIrrSym x $ \xDoc -> pppLambda PrecApp [xDoc] $ pppInf PrecLambda $ instantiate1Hreturn xDoc p
        , pppChk PrecApp z
        , pppChk PrecApp s
        , pppChk PrecApp n
        ]

#ifdef LANGUAGE_PTS_HAS_NAT_PRIM
pppInf d (TermPlus x y) = pppApplication d
    (pppText "ℕ-plus")
    [ pppChk PrecApp x
    , pppChk PrecApp y
    ]
pppInf d (TermTimes x y) = pppApplication d
    (pppText "ℕ-times")
    [ pppChk PrecApp x
    , pppChk PrecApp y
    ]
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
pppInf _ (Hadron qs) = pppHadron qs
pppInf d (QuarkElim x p qs q) = pppQuarkElim d x
    (\xDoc -> pppInf PrecLambda $ instantiate1Hreturn xDoc p)
    (fmap (pppChk PrecApp) qs)
    (pppChk PrecApp q)
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
#ifdef LANGUAGE_PTS_HAS_SIGMA
pppPeelPi (Sigma n a b)
{-
    | Just b' <- unusedScopeH b = do
        ~(xs, ys) <- pppPeelPi b'
        return (PPArrow (pppInf PrecPi a) : xs, ys)
-}
    | Sort a' <- a, a' == typeSort =
        pppScopedIrrSym n $ \nDoc -> do
            ~(xs, ys) <- pppPeelPi (instantiate1H (return nDoc) b)
            return (PPExists nDoc : xs, ys)
    | otherwise =
        pppScopedIrrSym n $ \nDoc -> do
            ~(xs, ys) <- pppPeelPi (instantiate1H (return nDoc) b)
            return (PPSigma nDoc (pppInf PrecPi a) : xs, ys)
#endif
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
    pppPeelLam (Lam n b) = pppScopedIrrSym n $ \nDoc -> do
        ~(xs, ys) <- pppPeelLam (instantiate1H (return nDoc) b)
        return (nDoc : xs, ys)
    pppPeelLam x   = do
        x' <- pppChk PrecLambda x
        return ([], return x')

#ifdef LANGUAGE_PTS_HAS_SIGMA
pppChk d (Pair x y) = pppApplication d
    "pair"
    [ pppChk PrecApp x
    , pppChk PrecApp y
    ]

pppChk d (Match p x y b) = pppApplication d
    (pppText "match")
    [ pppInf PrecApp p
    , pppScopedIrrSym x $ \xDoc -> pppScopedIrrSym y $ \yDoc ->
        pppLambda PrecApp [xDoc, yDoc] $ pppChk PrecLambda $ instantiate2Hreturn xDoc yDoc b
    ]
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
pppChk _ Refl = "refl"
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
pppChk d (Absurd x) = pppApplication d
    (pppText "absurd") [ pppChk PrecApp x ]
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
pppChk _ (Quark q) = pppQuark q
#endif

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

#ifdef LANGUAGE_PTS_HAS_SIGMA
    Sigma x a b >>= f =  Sigma x (a >>= f) (b >>== f)
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
    Equality a x y   >>= f = Equality (a >>= f) (x >>== f) (y >>== f)
    J v3 a p r u v w >>= f = J v3 (a >>= f) (p >>== f) (r >>== f) (u >>== f) (v >>== f) (w >>== f)
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
    Unit  >>= _ = Unit
    I     >>= _ = I
    Empty >>= _ = Empty
#endif

#ifdef LANGUAGE_PTS_HAS_BOOL
    TermBool               >>= _ = TermBool
    TermTrue               >>= _ = TermTrue
    TermFalse              >>= _ = TermFalse
    TermBoolElim x p z s n >>= k = TermBoolElim x
        (p >>== k)
        (z >>== k)
        (s >>== k)
        (n >>== k)

#ifdef LANGUAGE_PTS_HAS_BOOL_PRIM
    TermAnd x y >>= k = TermAnd (x >>== k) (y >>== k)
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_NAT
    TermNat             >>= _ = TermNat
    TermNatZ            >>= _ = TermNatZ
    TermNatS n          >>= k = TermNatS (n >>== k)
    TermNatElim x p z s n >>= k = TermNatElim x
        (p >>== k)
        (z >>== k)
        (s >>== k)
        (n >>== k)

#ifdef LANGUAGE_PTS_HAS_NAT_PRIM
    TermPlus x y >>= k = TermPlus (x >>== k) (y >>== k)
    TermTimes x y >>= k = TermTimes (x >>== k) (y >>== k)
#endif
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
    Hadron qs >>= _ = Hadron qs
    QuarkElim x p qs q >>= k = QuarkElim x
        (p >>== k)
        (fmap (>>== k) qs)
        (q >>== k)
#endif

instance Module (TermChk s) (TermInf s) where
    Inf u   >>== k = Inf (u >>= k)
    Lam n b >>== k = Lam n (b >>== k)

#ifdef LANGUAGE_PTS_HAS_SIGMA
    Pair x y      >>== k = Pair (x >>== k) (y >>== k)
    Match p x y b >>== k = Match (p >>= k) x y (b >>== k)
#endif

#ifdef LANGUAGE_PTS_HAS_EQUALITY
    Refl >>== _ = Refl
#endif

#ifdef LANGUAGE_PTS_HAS_PROP
    Absurd x >>== k = Absurd (x >>== k)
#endif

#ifdef LANGUAGE_PTS_HAS_QUARKS
    Quark q >>== _ = Quark q 
#endif

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

instance IsString a => Num (TermInf s a) where
    fromInteger n
#ifdef LANGUAGE_PTS_HAS_NAT
        | n <= 0    = TermNatZ
        | otherwise = TermNatS (Inf (fromInteger (pred n)))
#else
        = fromString (show n)
#endif

    n + m = App (App "plus" (Inf n)) (Inf m)
    n * m = App (App "times" (Inf n)) (Inf m)
    n - m = App (App "minus" (Inf n)) (Inf m)
    
    abs n    = App "abs" (Inf n)
    signum n = App "signum" (Inf n)
    negate n = App "negate" (Inf n)

instance IsString a => Num (TermChk s a) where
    fromInteger = Inf . fromInteger

    n + m = Inf (App (App "plus" n) m)
    n * m = Inf (App (App "times" n) m)
    n - m = Inf (App (App "minus" n) m)

    abs n    = Inf (App "abs" n)
    signum n = Inf (App "signum" n)
    negate n = Inf (App "negate" n)
