{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
module Language.PTS.Script (
    Script (..),
    spec_,
    ($$),
    runLoud,
    Loud,
    ) where

import Control.Lens
import Control.Monad.Except
import Control.Monad.IO.Class     (MonadIO (..))
import Control.Monad.State.Strict (MonadState, StateT, evalStateT)
import Data.Map.Strict            (Map)

import qualified Text.PrettyPrint.Compact as PP

import Language.PTS.Bound
import Language.PTS.Check
import Language.PTS.Error
import Language.PTS.Eval
import Language.PTS.Pretty
import Language.PTS.Specification
import Language.PTS.Sym
import Language.PTS.Term
import Language.PTS.Value

-------------------------------------------------------------------------------
-- Class
-------------------------------------------------------------------------------

-- | Scripts, monads for writing bigger terms.
--
-- See 'Language.PTS.Examples.churchBooleans' for an example.
--
class (Specification s, Monad m) => Script s m | m -> s where

    -- | Define a term with a type. Note, first argument is a type.
    define_
        :: Sym            -- ^ name
        -> Term s         -- ^ type
        -> TermChk s Sym  -- ^ term
        -> m ()

    -- | Evaluate an example value.
    example_ :: Term s -> m ()

    -- | Write a comment to be output.
    comment_ :: String -> m ()

-- | Tell used specification. Helps type-inference.
spec_ :: Script s m => s -> m ()
spec_ _ = return ()

infixl 0 $$
-- | '$' is __infixr__, '$$' is __infixl__
($$) :: (a -> b) -> a -> b
($$) = ($)

-------------------------------------------------------------------------------
-- Loud
-------------------------------------------------------------------------------

newtype Loud s a = Loud { _unLoud :: ExceptT Err (StateT (S s) IO) a }
  deriving (Functor, Applicative, Monad, MonadState (S s), MonadError Err)

instance MonadErr (Loud s) where
    throwErr = throwError

putPP :: PrettyM Doc -> Loud s ()
putPP = Loud . liftIO . prettyPutWith renderOpts

renderOpts :: PP.Options a String
renderOpts = PP.defaultOptions { PP.optsPageWidth = 60 }

data S s = S
    { _sTerms       :: !(Map Sym (Term s, Value s)) -- ^ defined terms
    , _sLastCommand :: !(Maybe C)                   -- ^ previous command
    , _sSection     :: !Int
    }

data C = CComment | CDefine | CExample deriving (Eq)

sTerms :: Lens' (S s) (Map Sym (Term s, Value s))
sTerms = lens _sTerms (\s x -> s { _sTerms = x })

sLastCommand :: Lens' (S s) (Maybe C)
sLastCommand = lens _sLastCommand (\s x -> s { _sLastCommand = x })

emptyS :: S s
emptyS = S
    { _sTerms       = mempty
    , _sLastCommand = Nothing
    , _sSection     = 0
    }

runLoud :: Loud s () -> IO ()
runLoud (Loud m) = evalStateT (runExceptT m) emptyS >>= \x -> case x of
    Left err -> prettyPut err
    Right () -> putStrLn "∎"

startCommand :: C -> Loud s ()
startCommand c = Loud $ do
    lc <- use sLastCommand
    sLastCommand ?= c

    case lc of
        Nothing                     -> pure ()
        Just CComment               -> pure ()
        Just CDefine | c == CDefine -> pure ()
        _ -> liftIO $ putStrLn "--"

-------------------------------------------------------------------------------
-- Loud instance
-------------------------------------------------------------------------------

instance Specification s => Script s (Loud s) where
    comment_ str = do
        startCommand CComment
        Loud $ liftIO $ putStrLn $ "-- " ++ str

    define_ n t x = do
        startCommand CDefine
        putPP $ "λ» :define" <+> ppp0 n
            </> pppColon <+> ppp0 t

            </> pppChar '=' <+> ppp0 x

        terms <- use sTerms
        when (has (ix n) terms) $ throwErr "Already defined"

        let typeCtx  n' = terms ^? ix n' . _2
        let valueCtx n' = case terms ^? ix n' . _1 of
                Nothing -> return n'
                Just y  -> y >>= valueCtx -- todo recursively add everything

        _ <- type_ typeCtx t >>= \s -> case s of
            ValueSort s' -> return s'
            _            -> throwErr "type of 'type' is not a sort"

        t' <- errorlessValueIntro (eval_ $ t >>= valueCtx)
        check_ typeCtx (x >>== valueCtx) t'

        -- putPP $ "checked type" </> ppp0 t'
        sTerms . at n ?= (Ann x t, t')

    example_ x = do
        startCommand CExample
        putPP $ "λ» :example" <+> ppp0 x
        terms <- use sTerms
        let typeCtx  n' = terms ^? ix n' . _2
        let valueCtx n' = case terms ^? ix n' . _1 of
                Nothing -> return n'
                Just y  -> y >>= valueCtx -- todo recursively add everything

        t <- type_ typeCtx x
        x' <- errorlessValueIntro (eval_ $ x >>= valueCtx)
        putPP $ pppChar '↪' <+> ppp0 (x' :: Value s)
            </> pppChar ':' <+> ppp0 t

{-
    define_ n term = do
        putPP $ "define:" <+> ppp0 n <+> PP.equals </> ppp0 term
        terms <- use sTerms
        let ctx n' = terms ^? ix n' . _2
        t <- type_ ctx term >>= errorlessValueIntro
        putPP $ ppp0 t
-}
