{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
-- | Errors. Not re-exported by "Language.PTS".
module Language.PTS.Error (
    MonadErr (..),
    Err (..),
    AsErr (..),
    ) where

import Prelude ()
import Prelude.Compat

import Control.Exception
import Control.Lens              (Prism', review)
import Control.Monad.Error.Class (MonadError (..))
import Data.String               (IsString (..))

import qualified Control.Monad.EitherK    as U
import qualified Control.Unification      as U
import qualified Data.Set                 as Set
import qualified Text.PrettyPrint.Compact as PP

import Language.PTS.Pretty
import Language.PTS.Sym


-- | A @MonadError Err@.
class Monad m => MonadErr m where
    throwErr :: Err -> m a

instance AsErr err => MonadErr (Either err) where
    throwErr = Left . review _Err

instance (AsErr err, Monad m) => MonadErr (U.EitherKT err m) where
    throwErr = throwError . review _Err

-- | Throws 'Err' with 'throwIO'.
instance MonadErr IO where
    throwErr = throwIO

instance MonadErr Maybe where
    throwErr _ = Nothing

-------------------------------------------------------------------------------
-- Fallible
-------------------------------------------------------------------------------

instance (PrettyPrec1 t, PrettyPrec v) => U.Fallible t v Err where
    occursFailure v t   = OccursFailure (ppp PrecDef v) (ppp1 PrecDef t)
    mismatchFailure a b = MismatchFailure (ppp1 PrecDef a) (ppp1 PrecDef b)

-------------------------------------------------------------------------------
-- Class
-------------------------------------------------------------------------------

class AsErr e where
    _Err :: Prism' e Err

instance AsErr Err where
    _Err = id

-------------------------------------------------------------------------------
-- Err
-------------------------------------------------------------------------------

-- | Various errors occuring during type-checking of terms.
data Err
    = SomeErr String
      -- ^ /untyped/ error. Avoid.
    | VariableNotInScope (PrettyM Doc) [PrettyM Doc]
      -- ^ variable not in the context provided
    | TypeMismatch (PrettyM Doc) (PrettyM Doc) (PrettyM Doc) [PrettyM Doc]
      -- ^ type mismatch in function application
    | NonEqual (PrettyM Doc) (PrettyM Doc) (PrettyM Doc) [PrettyM Doc]
      -- ^ Refl annotated with mismatching values
    | SortMismatch (PrettyM Doc) (PrettyM Doc) (PrettyM Doc) [PrettyM Doc]
      -- ^ type mismatch in function application
    | LambdaNotPi (PrettyM Doc) (PrettyM Doc) [PrettyM Doc]
      -- ^ Lambda is (annotated with) not a Pi-type
    | PairNotSigma (PrettyM Doc) (PrettyM Doc) [PrettyM Doc]
      -- ^ Pair is (annotated with) not a Sigma-type
    | ReflNotEquality (PrettyM Doc) [PrettyM Doc]
      -- ^ Refl is (annotated with) not an Equality-type
    | NotAPair (PrettyM Doc) (PrettyM Doc) [PrettyM Doc]
      -- ^ Match on not a pair
    | NoRule (PrettyM Doc) (PrettyM Doc) [PrettyM Doc]
      -- ^ invalid function space
    | NotAFunction (PrettyM Doc) (PrettyM Doc) (PrettyM Doc) [PrettyM Doc]
      -- ^ apply warning in 'Term' type-checker.
    | SortWithoutAxiom (PrettyM Doc) [PrettyM Doc]
      -- ^ abstracting over a sort without an axiom.
    | QuarkNotInHadron Sym (Set.Set Sym) [PrettyM Doc]
      -- ^ quark not in hardon
    | QuarkNotHadron Sym (PrettyM Doc) [PrettyM Doc]
      -- ^ quark is (annoted with) not a hadron
    | ApplyPanic String (PrettyM Doc)
      -- ^ apply panic in 'Value' evaluator
    | OccursFailure (PrettyM Doc) (PrettyM Doc)
      -- ^ Occurs failure, i.e infinite type
    | MismatchFailure (PrettyM Doc) (PrettyM Doc)

instance Show Err where
    -- TODO: use renderWith
    showsPrec _ = showString . prettyShow

instance Exception Err

instance IsString Err where
    fromString = SomeErr

instance PrettyPrec Err where
    ppp _ (SomeErr err)                   = pppError [] [pppText err]
    ppp _ (VariableNotInScope x ctx)      = pppError ctx
        [ "Variable not in scope" <+> x
        ]
    ppp _ (TypeMismatch expt act term ctx) = pppError ctx
        [ "Couldn't match expected type" <+> expt <+> "with actual type" <+> act
        , "In the expression:" <+> term
        ]
    ppp _ (SortMismatch expt act term ctx) = pppError ctx
        [ "Couldn't match expected sort" <+> expt <+> "with actual type" <+> act
        , "In the expression:" <+> term
        ]
    ppp _ (LambdaNotPi t term ctx)         = pppError ctx
        [ "The lambda expression" <+> term <+> "doesn't have a Pi-type"
        , "Annotated with" <+> t
        ]
    ppp _ (PairNotSigma t term ctx)        = pppError ctx
        [ "The pair expression" <+> term <+> "doesn't have a Sigma-type"
        , "Annotated with" <+> t
        ]
    ppp _ (ReflNotEquality t ctx)          = pppError ctx
        [ "The refl doesn't have a Equality-type"
        , "Annotated with" <+> t
        ]
    ppp _ (NonEqual x y a ctx)             = pppError ctx
        [ "Couldn't match expected value" <+> x <+> "with value" <+> y
        , "Equality of the type:" <+> a
        ]
    ppp _ (NoRule s1 s2 ctx)               = pppError ctx
        [ "No PTS Rule (" <> s1 <> "," <> s2 <> ",-)"
        ]
    ppp _ (NotAFunction t f x ctx)         = pppError ctx
        [ "Couldn't match actual type" <+> t <+> "with a function type"
        , "In the application of" <+> f
        , "to the value" <+> x
        ]
    ppp _ (NotAPair t p ctx)               = pppError ctx
        [ "Couldn't match actual type" <+> t <+> "with a pair type"
        , "In the match on" <+> p
        ]
    ppp _ (QuarkNotInHadron q qs ctx)      = pppError ctx
        [ "The quark" <+> pppQuark q <+> "is not in hadron" <+> pppHadron qs
        ]
    ppp _ (QuarkNotHadron q t ctx)         = pppError ctx
        [ "The quark" <+> pppQuark q <+> "doesn't have a Hadron type"
        , "Annotated with" <+> t
        ]
    ppp _ (SortWithoutAxiom s ctx)         = pppError ctx
        [ "Type-less sort" <+> s <+> "(no axiom exist)"
        ]
    ppp _ (ApplyPanic tag f) =
        "panic '" <> pppText tag <> "':" </> err
      where
        err = "Trying to apply not-a-lambda" <+> f

    ppp _ (OccursFailure v t)  = pppError []
        [ "Occurs check, cannot construct infinite type" <+> v <+> " ~ " <+> t
        ]
    ppp _ (MismatchFailure a b) = pppError []
        [ "Couldn't match expected type" <+> b <+> "with actual type" <+> a
        ]

pppError :: [PrettyM Doc] -> [PrettyM Doc] -> PrettyM Doc
pppError [] bs = "error:" $$$ pppBullets bs
pppError ts bs = "error:" $$$ pppBullets (bs ++ [err]) where
    err = "when checking expression" $$$ fmap PP.vcat (sequence ts)

pppBullets :: [PrettyM Doc] -> PrettyM Doc
pppBullets bs = PP.vcat <$> traverse (pppChar '•' <+>) bs
