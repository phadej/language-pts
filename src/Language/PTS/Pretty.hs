{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | TODO The syntax is quite light, so the precedence table is small:
--
-- +-------------+-------+--------------------------------------+
-- | operation   | assoc | examples                             |
-- +=============+=======+======================================+
-- | application | left  | @f x y@, @f (g x)@                   |
-- +-------------+-------+--------------------------------------+
-- | Pi,arrow    | right | @a -> b -> c@, @(a -> b) -> c@       |
-- +-------------+-------+--------------------------------------+
-- | lambda      | none  | @λx → x@                          |
-- +-------------+-------+--------------------------------------+
-- | annotation  | right | @a : t@, @a : t : s@, @(a : t) : t'@ |
-- +-------------+-------+--------------------------------------+
--
-- %>>> let pp  = prettyPut :: Term LambdaStar -> IO ()
-- %>>> let pp' = prettyPut :: Value LambdaStar -> IO ()
-- %>>> let s   = LambdaStar
--
-- %>>> pp $ "f" @@ "x" @@ "y"
-- f x y
--
-- %>>> pp $ pi_ "m" ("Nat" ~> sort_ s) s ("m" @@ "zero" ~> "x") s
-- ∏m : Nat → ⋆. m zero → x
--
-- %>>> pp' $ lam_ "x" "x"
-- λx → x
--
-- %>>> prettyPut ("x" -:- "t" -:- "s" :: Term LambdaStar)
-- x : t : s
--
-- %>>> prettyPut (("x" -:- "t") -:- "s" :: Term LambdaStar)
-- (x : t) : s
--
-- /Note:/ we don't rename or disambiguate variables (in pretty-printing),
-- so one have to be careful:
--
-- %>>> let latter = lams_ ["x", "x"] "x" :: Value LambdaStar
-- %>>> let former = lams_ ["f", "x"] ("f" `valueApp` "x") `valueApp` lams_ ["y", "x"] "y" :: Value LambdaStar
--
-- %>>> pp' latter
-- λx x → x
--
-- %>>> pp' former
-- λx x → x
--
-- but they are different:
--
-- %>>> print latter >> print former
-- ValueLam "x" (Scope (ValueLam "x" (Scope (ValueCoerce (ValueVar (B "x"))))))
-- ValueLam "x" (Scope (ValueLam "x" (Scope (ValueCoerce (ValueVar (F (B "x")))))))
--
module Language.PTS.Pretty (
    -- * Class
    PrettyPrec (..),
    PrettyM, Doc,
    ppp0,
    pppParens,
    PrettyPrec1 (..),
    ppp1,
    -- * Convience functons
    prettyShow,
    prettyShowWith,
    prettyPut,
    prettyPutWith,
    -- * Symbols
    pppMarkSym,
    pppFreshSym,
    pppScopedSym,
    pppScopedIrrSym,
    -- * Combinators
    -- | The @pretty-compact@ combinators wrapped in 'PrettyM'.
    pppChar, pppText, pppIntegral, pppIntegralSub,
    (<+>), (</>), ($$$),
    pppHsepPunctuated,
    pppSepPunctuated,
    pppCatPunctuated,
    pppColon,
    pppComma_,
    pppHang,
    -- * Syntax
    -- | Combinators for different syntactical constructs.
    pppApplication,
    pppPi,
    PPPi (..),
    pppLambda,
    pppAnnotation,
    pppAnnotationPi,
    -- * Hadron
    pppHadron,
    pppQuark,
    pppQuarkElim,
    -- * Precedence
    Prec (..),
    predPrec,
    ) where

import Prelude ()
import Prelude.Compat

import Bound.Name                 (Name (..))
import Bound.Var                  (Var (..))
import Control.Applicative        (liftA2)
import Control.Lens               (itraverse)
import Control.Monad.State.Strict
import Data.Char                  (isDigit)
import Data.String                (IsString (..))
import Data.Text                  (Text, pack, unpack)
import Data.Void                  (Void, absurd)

import qualified Control.Unification        as U
import qualified Control.Unification.IntVar as U
import qualified Data.Map                   as Map
import qualified Data.Set                   as Set
import qualified Text.PrettyPrint.Compact   as PP

import Language.PTS.Sym

-------------------------------------------------------------------------------
-- Prec
-------------------------------------------------------------------------------

data Prec
    = PrecDef
    | PrecAnn
    | PrecLambda
    | PrecPi
    | PrecApp
  deriving (Eq, Ord, Show)

predPrec :: Prec -> Prec
predPrec PrecDef  = PrecDef
predPrec PrecAnn    = PrecDef
predPrec PrecLambda = PrecAnn
predPrec PrecPi     = PrecLambda
predPrec PrecApp    = PrecPi

-------------------------------------------------------------------------------
-- Pretty class
-------------------------------------------------------------------------------

type Doc = PP.Doc ()

-- | State of pretty-printer's "used" symbols
type S = Set.Set U

-- | A pretty-printing monad, keeping state of binded symbols.
newtype PrettyM a = PrettyM { unPrettyM :: State S a }
  deriving (Functor, Applicative, Monad)

runPrettyM :: PrettyM a -> a
runPrettyM (PrettyM m) = evalState m Set.empty

instance a ~ Doc => IsString (PrettyM a) where
    fromString = return . PP.text

instance a ~ Doc => Semigroup (PrettyM a) where
    (<>) = liftA2 (<>)

instance a ~ Doc => Monoid (PrettyM a) where
    mempty  = pure mempty
    mappend = (<>)

class PrettyPrec a where
    ppp ::  Prec ->  a -> PrettyM Doc

instance a ~ Doc => PrettyPrec (PrettyM a) where
    ppp _ doc = doc

prettyShow :: PrettyPrec a => a -> String
prettyShow = PP.render . runPrettyM . ppp PrecDef

prettyShowWith :: PrettyPrec a => PP.Options () String -> a -> String
prettyShowWith opts = PP.renderWith opts . runPrettyM . ppp PrecDef

prettyPut :: PrettyPrec a => a -> IO ()
prettyPut = putStrLn . prettyShow

prettyPutWith :: PrettyPrec a => PP.Options () String -> a -> IO ()
prettyPutWith opts = putStrLn . PP.renderWith opts . runPrettyM . ppp PrecDef

ppp0 :: PrettyPrec a => a -> PrettyM Doc
ppp0 = ppp PrecDef

class PrettyPrec1 f where
    liftPpp
        :: (Prec ->   a -> PrettyM Doc)
        -> Prec  -> f a -> PrettyM Doc

-- | Helper useful to define `PrettyPrec` in terms of `PrettyPrec1`.
ppp1 :: (PrettyPrec1 f,  PrettyPrec a) => Prec -> f a -> PrettyM Doc
ppp1 = liftPpp ppp

pppParens :: Bool -> PrettyM Doc -> PrettyM Doc
pppParens True = fmap PP.parens
pppParens _    = id

-- | Mark symbol name as used, but print it as is
--
-- >>> prettyPut' $ pppMarkSym "x" <+> pppMarkSym "x" <+> pppFreshSym "x"
-- x x x₁
--
pppMarkSym :: Sym -> PrettyM Doc
pppMarkSym (Sym s) = PrettyM $ do
    let u = toU s
    xs <- get
    put (Set.insert u xs)
    return (PP.text (unpack s))

-- | Generate fresh name.
--
-- >>> prettyPut' $ pppFreshSym "x" <+> pppFreshSym "x" <+> pppFreshSym "x"
-- x x₁ x₂
--
pppFreshSym :: Sym -> PrettyM Doc
pppFreshSym (Sym s) = PrettyM $ do
    xs <- get
    let u = freshU xs (genU (toU s))
    put (Set.insert u xs)
    return (PP.text (fromU u))

-- | Scoped name usage. See 'PrettyPrec
--
-- >>> prettyPut $ pppFreshSym "x" <+> pppParens True (pppScopedSym "x" (\x -> "\\" <> return x <> "...")) <+> pppFreshSym "x"
-- x (\x₁...) x₁
--
pppScopedSym :: Sym -> (Doc -> PrettyM a) -> PrettyM a
pppScopedSym (Sym s) f
    | s == pack "_"    = f (PP.char '_')
pppScopedSym (Sym s) f = PrettyM $ do
    xs <- get
    let u = freshU xs (genU (toU s))
    put (Set.insert u xs)
    x <- unPrettyM (f (PP.text (fromU u)))
    modify' (Set.delete u)
    return x

pppScopedIrrSym :: IrrSym -> (Doc -> PrettyM a) -> PrettyM a
pppScopedIrrSym (IrrSym s) = pppScopedSym s

-------------------------------------------------------------------------------
-- U
-------------------------------------------------------------------------------

data U = U !Int !Text deriving (Eq, Ord)

genU :: U -> Stream U
genU u@(U n t) = u :> genU (U (succ n) t)

freshU :: Set.Set U -> Stream U -> U
freshU xs (y :> ys)
    | Set.member y xs = freshU xs ys
    | otherwise       = y

toU :: Text -> U
toU t
    | null ds   = U 0 t
    | otherwise = U (read (reverse ds)) (pack (reverse rn))
  where
    (ds, rn) = span isDigit (reverse (map unsubDigit (unpack t)))

fromU :: U -> String
fromU (U n t)
    | n <= 0    = unpack t
    | otherwise = unpack t ++ map subDigit (show n)
  where

data Stream a = a :> Stream a

-------------------------------------------------------------------------------
-- Syntax
-------------------------------------------------------------------------------

-- | Render application.
--
-- >>> prettyPut' $ pppApplication PrecDef "f" ["a", "b", "c", "d"]
-- f a b c d
--
-- >>> prettyPut' $ pppApplication PrecDef "f" ["aaaa", "bbbb", "cccc", "dddd"]
-- f aaaa
--   bbbb
--   cccc
--   dddd
--
pppApplication :: Prec -> PrettyM Doc -> [PrettyM Doc] -> PrettyM Doc
pppApplication d f xs = pppParens (d >= PrecApp) $ pppHang 4 f (pppSep xs)

-- | Specifies how to print (function) types.
data PPPi
    = PPPi Doc (PrettyM Doc)
    | PPForall Doc
    | PPArrow (PrettyM Doc)
    | PPSigma Doc (PrettyM Doc)
    | PPExists Doc

-- | Render (dependent) function space.
--
-- >>> prettyPut' $ pppPi PrecDef [PPPi "n" "Nat"] "Vec a n"
-- ∏ (n : Nat) →
-- Vec a n
--
-- >>> prettyPut' $ pppPi PrecDef [PPPi "n" "Nat", PPForall "a"] "Vec a n"
-- ∏ (n : Nat) →
-- ∀ a →
-- Vec a n
--
-- >>> prettyPut' $ pppPi PrecDef [PPPi "n" "Nat", PPForall "a", PPArrow "Vec a n"] "r"
-- ∏ (n : Nat) →
-- ∀ a →
-- Vec a n →
-- r
--
-- >>> prettyPut' $ pppPi PrecDef [PPArrow (pppPi PrecPi [PPArrow "a"] "b"), PPArrow "a"] "b"
-- (a → b) → a → b
--
pppPi :: Prec -> [PPPi] -> PrettyM Doc -> PrettyM Doc
pppPi _ [] x = x
pppPi d vs x = pppParens (d >= PrecPi) $
    pppSepPunctuated' pppArrow_ (map pppPiPart vs ++ [x]) where


-- | Render lambda abstraction.
--
-- >>> prettyPut' $ pppLambda PrecDef [] "x"
-- x
--
-- >>> prettyPut' $ pppLambda PrecDef ["x", "y", "z"] "long body"
-- λ x y z →
--     long body
--
pppLambda :: Prec -> [Doc] -> PrettyM Doc -> PrettyM Doc
pppLambda _ [] x = x
pppLambda d vs x = pppParens (d >= PrecLambda) $
    pppHang 4 (pppChar 'λ' <+> return (PP.hsep vs) <+> return pppArrow_) x

-- | Render type annotation.
pppAnnotation :: Prec -> PrettyM Doc -> PrettyM Doc -> PrettyM Doc
pppAnnotation d x t = pppParens (d >= PrecAnn) $
    pppHang 4 x (pppColon <+> t)

-- | Render type annotation with (possibly) pi-type.
--
-- >>> prettyPut' $ pppAnnotationPi PrecDef "x" [] "t"
-- x : t
--
-- >>> prettyPut' $ pppAnnotationPi PrecDef "f" [PPArrow (pppPi PrecPi [PPArrow "a"] "b"), PPArrow "a"] "b"
-- f : (a → b)
--   → a
--   → b
--
-- >>> prettyPut' $ pppAnnotationPi PrecDef "myfunc" [PPPi "n" "Nat", PPForall "a", PPArrow "Vec a n"] "r"
-- myfunc
--     : ∏ (n : Nat)
--     → ∀ a
--     → Vec a n
--     → r
--
pppAnnotationPi :: Prec -> PrettyM Doc -> [PPPi] -> PrettyM Doc -> PrettyM Doc
pppAnnotationPi d x []       t = pppAnnotation d x t
pppAnnotationPi d x (s : ss) t = pppParens (d >= PrecAnn) $
    pppHang 4 x $ pppSep
        $ (pppColon <+> pppPiPart s)
        : map (\s' -> pppArrow <+> pppPiPart s') ss
        ++ [pppArrow <+> t]

-- change to "∏"
pppPiPart :: PPPi -> PrettyM Doc
pppPiPart (PPPi n t)    = pppChar '∏' <+> pppParens True (return n <+> pppColon <+> t)
pppPiPart (PPForall n)  = pppChar '∀' <+> return n
pppPiPart (PPArrow n)   = n
pppPiPart (PPExists n)  = pppChar 'E' <+> return n
pppPiPart (PPSigma n t) = pppChar '∑' <+> pppParens True (return n <+> pppColon <+> t)

-------------------------------------------------------------------------------
-- Hadron
-------------------------------------------------------------------------------

pppHadron :: Set.Set Sym -> PrettyM Doc
pppHadron s
    | null s    = pure (PP.braces mempty)
    | otherwise = PP.braces . PP.hsep <$> traverse pppQuark s'
  where
    s' = Set.toList s

pppQuark :: Sym -> PrettyM Doc
pppQuark (Sym t) = pppText $ ':' : unpack t

pppQuarkElim
    :: Prec
    -> IrrSym
    -> (Doc -> PrettyM Doc)
    -> Map.Map Sym (PrettyM Doc)
    -> PrettyM Doc
    -> PrettyM Doc
pppQuarkElim d x p qs q = pppApplication d
    (pppText "ℚ-elim")
    [ pppScopedIrrSym x $ \xDoc -> pppLambda PrecApp [xDoc] $ p xDoc
    , q
    , cases
    ]
  where
    cases | null qs   = pure (PP.braces pppArrow_)
          | otherwise = PP.semiBraces . Map.elems <$> itraverse case_ qs

    case_ k v = pppQuark k <+> pppArrow <+> v

-------------------------------------------------------------------------------
-- Combinators
-------------------------------------------------------------------------------

pppChar :: Char -> PrettyM Doc
pppChar = return . PP.char

pppText :: String -> PrettyM Doc
pppText = return . PP.text

pppIntegral :: Integral a => a -> PrettyM Doc
pppIntegral = return . PP.integer . fromIntegral

pppIntegralSub :: Integral a => a -> PrettyM Doc
pppIntegralSub
    = return . PP.text
    . map subDigit . (show :: Integer -> String)
    . fromIntegral

infixr 6 <+>
infixr 5 $$$, </>

(<+>) :: PrettyM Doc -> PrettyM Doc -> PrettyM Doc
(<+>) = liftA2 (PP.<+>)

(</>) :: PrettyM Doc -> PrettyM Doc -> PrettyM Doc
(</>) = liftA2 (PP.</>)

($$$) :: PrettyM Doc -> PrettyM Doc -> PrettyM Doc
($$$) = liftA2 (PP.$$)

pppHang :: Int -> PrettyM Doc -> PrettyM Doc -> PrettyM Doc
pppHang n = liftA2 (PP.hang n)

pppSep :: [PrettyM Doc] -> PrettyM Doc
pppSep = fmap PP.sep . sequence

pppSepPunctuated' :: Doc -> [PrettyM Doc] -> PrettyM Doc
pppSepPunctuated' x ys = PP.sep . punctuate' x <$> sequence ys

pppSepPunctuated :: Doc -> [PrettyM Doc] -> PrettyM Doc
pppSepPunctuated x ys = PP.sep . PP.punctuate x <$> sequence ys

pppCatPunctuated :: Doc -> [PrettyM Doc] -> PrettyM Doc
pppCatPunctuated x ys = PP.cat . PP.punctuate x <$> sequence ys

punctuate' :: PP.Doc () -> [PP.Doc ()] -> [PP.Doc ()]
punctuate' _p []     = []
punctuate' _p [d]    = [d]
punctuate' p (d:ds)  = (d PP.<+> p) : punctuate' p ds

pppHsepPunctuated :: Doc -> [PrettyM Doc] -> PrettyM Doc
pppHsepPunctuated x ys = PP.hsep . PP.punctuate x <$> sequence ys

-------------------------------------------------------------------------------
-- Punctuation
-------------------------------------------------------------------------------

pppColon :: PrettyM Doc
pppColon = return PP.colon

pppComma_ :: PP.Doc ()
pppComma_ = PP.comma

pppArrow :: PrettyM Doc
pppArrow = pppChar '→'

pppArrow_ :: PP.Doc ()
pppArrow_ = PP.char '→'

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

liftPppVar
    :: (Prec ->     a   -> PrettyM Doc)
    -> (Prec ->       b -> PrettyM Doc)
    ->  Prec -> Var a b -> PrettyM Doc
liftPppVar f _ d (B x) = f d x
liftPppVar _ g d (F y) = g d y

instance PrettyPrec a => PrettyPrec1 (Var a) where
    liftPpp = liftPppVar ppp

instance PrettyPrec Void where
    ppp _ = absurd

instance PrettyPrec () where
    ppp _ _ = pppText "#var"

instance PrettyPrec1 Maybe where
    liftPpp _ _ Nothing  = pppText "Nothing"
    liftPpp p d (Just x) = p d x

instance PrettyPrec a => PrettyPrec (Maybe a) where
    ppp = ppp1

instance (PrettyPrec a, PrettyPrec b) => PrettyPrec (Either a b) where
    ppp d (Left x)  = ppp d x
    ppp d (Right y) = ppp d y

instance (PrettyPrec a, PrettyPrec b) => PrettyPrec (a, b) where
    ppp _ (x, y) = pppParens True $ ppp PrecDef x <+> pppChar ',' <+> ppp PrecDef y

-------------------------------------------------------------------------------
-- unification-fd
-------------------------------------------------------------------------------

instance PrettyPrec1 t => PrettyPrec1 (U.UTerm t) where
    liftPpp p = go where
        go d (U.UVar v)  = p d v
        go d (U.UTerm t) = liftPpp go d t

instance (PrettyPrec1 t, PrettyPrec a) => PrettyPrec (U.UTerm t a) where ppp = ppp1

instance PrettyPrec U.IntVar where
    ppp _ (U.IntVar n) = pppChar '?' <> pppIntegral (n + minBound)

-------------------------------------------------------------------------------
-- bound
-------------------------------------------------------------------------------

instance PrettyPrec n => PrettyPrec (Name n a) where
    ppp d (Name n _) = ppp d n

instance (PrettyPrec a, PrettyPrec b) => PrettyPrec (Var a b) where
    ppp = ppp1

-------------------------------------------------------------------------------
-- Sym
-------------------------------------------------------------------------------

-- | Generates fresh names.
--
-- Uses 'pppMarkSym', see also 'pppFreshSym', and 'pppScopedSym'.
--
-- >>> prettyPut $ ppp0 ("x" :: Sym)
-- x
--
-- >>> prettyPut $ ppp0 ("x2" :: Sym)
-- x₂
--
instance PrettyPrec Sym where
    ppp _ = pppMarkSym

instance PrettyPrec IrrSym where
    ppp d (IrrSym s) = ppp d s

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> renderOpts = PP.defaultOptions { PP.optsPageWidth = 16 }
-- >>> prettyPut' = prettyPutWith renderOpts . (id :: PrettyM Doc -> PrettyM Doc)
--
-- >> import Language.PTS
-- >> import Language.PTS.Systems
