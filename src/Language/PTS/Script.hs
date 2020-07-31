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
    runSilent,
    runString,
    ScriptT,
    ) where

import Control.Lens
import Control.Monad.Except
import Control.Monad.State.Strict (MonadState, runState, State, StateT, evalStateT)
import Data.Foldable (for_)
import Data.Map.Strict            (Map)
import Data.Void                  (Void)

import qualified Text.PrettyPrint.Compact as PP

import Language.PTS.Bound
import Language.PTS.Check
import Language.PTS.Error
import Language.PTS.Pretty
import Language.PTS.Quote
import Language.PTS.Specification
import Language.PTS.Sym
import Language.PTS.Term
import Language.PTS.Value
import Language.PTS.Parametricity

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
    define_ = defineChk_

    defineChk_
        :: Sym            -- ^ name
        -> Term s         -- ^ type
        -> TermChk s Sym  -- ^ term
        -> m ()

    defineInf_
        :: Sym            -- ^ name
        -> Term s         -- ^ term
        -> m ()

    postulate_
        :: Sym            -- ^ name
        -> Term s         -- ^ type
        -> m ()

    parametricity_
        :: ReflectiveSpecification s
        => Term s
        -> m ()

    -- | Evaluate an example value.
    example_ :: Term s -> m ()

    -- | Write a comment to be output.
    comment_ :: String -> m ()

    section_    :: String -> m ()
    subsection_ :: String -> m ()

    -- | Dump definitions
    dumpDefs_ :: m ()

-- | Tell used specification. Helps type-inference.
spec_ :: Script s m => s -> m ()
spec_ _ = return ()

infixl 0 $$
-- | '$' is __infixr__, '$$' is __infixl__
($$) :: (a -> b) -> a -> b
($$) = ($)

-------------------------------------------------------------------------------
-- ScriptT
-------------------------------------------------------------------------------

newtype ScriptT s m a = ScriptT { _unScriptT :: ExceptT Err (StateT (S m s) m) a }
  deriving (Functor, Applicative, Monad, MonadError Err, MonadState (S m s))

instance Monad m => MonadErr (ScriptT s m) where
    throwErr = ScriptT . throwError

putPP :: Monad m => PrettyM Doc -> ScriptT s m ()
putPP doc = ScriptT $ do
    put <- use sPutStrLn
    w   <- use sWidth
    lift $ lift $ put $ prettyShowWith (renderOpts w) doc

renderOpts :: Int -> PP.Options a String
renderOpts w = PP.defaultOptions { PP.optsPageWidth = w }

data S m s = S
    { _sTerms       :: !(Map Sym (Term s, Value s)) -- ^ defined terms
    , _sDefinitions :: ![(Sym, Term s)]             -- ^ terms in a /reverse/ definition order
    , _sLastCommand :: !(Maybe C)                   -- ^ previous command
    , _sSection     :: !Int
    , _sSubsection  :: !Int
    , _sOutput      :: !Bool
    , _sWidth       :: !Int
    , _sPutStrLn    :: String -> m ()
    }

data C = CComment | CHeader | CDefine | CExample deriving (Eq)

sTerms :: Lens' (S m s) (Map Sym (Term s, Value s))
sTerms = lens _sTerms (\s x -> s { _sTerms = x })

sDefinitions :: Lens' (S m s) [(Sym, Term s)]
sDefinitions = lens _sDefinitions (\s x -> s { _sDefinitions = x })

sLastCommand :: Lens' (S m s) (Maybe C)
sLastCommand = lens _sLastCommand (\s x -> s { _sLastCommand = x })

sSection :: Lens' (S m s) Int
sSection = lens _sSection (\s x -> s { _sSection = x })

sSubsection :: Lens' (S m s) Int
sSubsection = lens _sSubsection (\s x -> s { _sSubsection = x })

sOutput :: Lens' (S m s) Bool
sOutput = lens _sOutput (\s x -> s { _sOutput = x })

sPutStrLn :: Lens' (S m s) (String -> m ())
sPutStrLn = lens _sPutStrLn (\s x -> s { _sPutStrLn = x })

sWidth :: Lens' (S m s) Int
sWidth = lens _sWidth (\s x -> s { _sWidth = x })

emptyS :: (String -> m ()) -> S m s
emptyS put = S
    { _sTerms       = mempty
    , _sDefinitions = []
    , _sLastCommand = Nothing
    , _sSection     = 0
    , _sSubsection  = 0
    , _sOutput      = True
    , _sWidth       = 60
    , _sPutStrLn    = put
    }

runLoud :: ScriptT s IO () -> IO ()
runLoud (ScriptT m) = do
    x <- evalStateT (runExceptT m) $ emptyS putStrLn
    case x of
        Left err -> prettyPut err
        Right () -> putStrLn "∎"

runSilent :: ScriptT s IO () -> IO ()
runSilent (ScriptT m) = do
    x <- evalStateT (runExceptT m) $ (emptyS putStrLn) { _sOutput = False }
    case x of
        Left err -> prettyPut err
        Right () -> putStrLn "∎"

runString :: ScriptT s (State ([String] -> [String])) () -> String
runString (ScriptT m) = unlines $
    case runState (evalStateT (runExceptT m) $ (emptyS put) { _sWidth = 120 } ) id of
        (Left err, f) -> f [prettyShow err]
        (Right (), f) -> f ["∎"]
  where
    put :: String -> State ([String] -> [String]) ()
    put str = do
        f <- use id
        id .= (f . (str :))

startCommand :: Monad m => C -> ScriptT s m ()
startCommand c = ScriptT $ do
    lc <- use sLastCommand
    sLastCommand ?= c

    case lc of
        Nothing                      -> pure ()
        Just CComment | c /= CHeader -> pure ()
        Just CDefine | c == CDefine  -> pure ()
        _ -> _unScriptT $ loudPutStrLn "--"

loudPutStrLn :: Monad m => String -> ScriptT s m ()
loudPutStrLn str = ScriptT $ do
    output <- use sOutput
    put    <- use sPutStrLn
    when output $ lift $ lift $ put str

-------------------------------------------------------------------------------
-- ScriptT instance
-------------------------------------------------------------------------------

instance (Specification s, Monad m) => Script s (ScriptT s m) where
    comment_ str = do
        startCommand CComment
        loudPutStrLn $ "-- " ++ str

    section_ str = ScriptT $ do
        _unScriptT $ startCommand CHeader
        n <- use sSection
        sSection .= n + 1
        sSubsection .= 0
        let title = "-- " ++ show (n + 1) ++ ". " ++ str
        _unScriptT $ loudPutStrLn title
        _unScriptT $ loudPutStrLn $ '-' <$ title

    subsection_ str = ScriptT $ do
        _unScriptT $ startCommand CHeader
        n <- use sSection
        m <- use sSubsection
        sSubsection .= m + 1
        _unScriptT $ loudPutStrLn $ "-- " ++ show n ++ "." ++ show (m + 1) ++ ". " ++ str

    defineChk_ n t x = do
        startCommand CDefine
        output <- ScriptT $ use sOutput

        if output
        then putPP $ "λ» :define" <+> ppp0 n
                </> pppColon <+> ppp0 t
                </> pppChar '=' <+> ppp0 x
        else do
            let xDoc = ppp0 x
            let str = prettyShowWith (PP.defaultOptions { PP.optsPageWidth = maxBound }) xDoc
                str' = let (pfx, sfx) = splitAt 20 str in pfx ++ takeWhile (/= ' ') sfx
            let doc = if length str > 20 then pppText $ str' ++ ".." else xDoc
            putPP $ "λ» :define" <+> ppp0 n
                </> pppColon <+> ppp0 t
                </> pppChar '=' <+> doc

        terms <- use sTerms
        when (has (ix n) terms) $ throwErr "Already defined"

        let typeCtx  n' = terms ^? ix n' . _2
        let valueCtx n' = maybe (return n') id $ terms ^? ix n' . _1

        let t' = t >>= valueCtx
        (t'', tt) <- type_ typeCtx t'
        case tt of
            ValueSort _ -> return ()
            _           -> throwErr "type of 'type' is not a sort"

        let x' = x >>== valueCtx
        _ <- check_ typeCtx x' t''

        -- putPP $ "checked type" </> ppp0 t'
        sTerms . at n ?= (Ann x' t', t'')
        sDefinitions %= ((n, Ann x t) :)

    defineInf_ n x = do
        startCommand CDefine
        output <- ScriptT $ use sOutput

        if output
        then putPP $ "λ» :define" <+> ppp0 n
                </> pppChar '=' <+> ppp0 x
        else do
            let xDoc = ppp0 x
            let str = prettyShowWith (PP.defaultOptions { PP.optsPageWidth = maxBound }) xDoc
                str' = let (pfx, sfx) = splitAt 20 str in pfx ++ takeWhile (/= ' ') sfx
            let doc = if length str > 20 then pppText $ str' ++ ".." else xDoc
            putPP $ "λ» :define" <+> ppp0 n
                </> pppChar '=' <+> doc

        terms <- use sTerms
        when (has (ix n) terms) $ throwErr "Already defined"

        let typeCtx  n' = terms ^? ix n' . _2
        let valueCtx n' = maybe (return n') id $ terms ^? ix n' . _1

        let x' = x >>= valueCtx
        (_, t) <- type_ typeCtx x'

        sTerms . at n ?= (x', t)
        sDefinitions %= ((n, x) :)

    postulate_ n t = do
        startCommand CDefine
        output <- ScriptT $ use sOutput

        if output
        then putPP $ "λ» :postulate" <+> ppp0 n
                </> pppColon <+> ppp0 t
        else return ()

        terms <- use sTerms
        when (has (ix n) terms) $ throwErr "Already defined"

        let typeCtx  n' = terms ^? ix n' . _2
        let valueCtx n' = maybe (return n') id $ terms ^? ix n' . _1

        let t' = t >>= valueCtx
        (t'', tt) <- type_ typeCtx t'
        case tt of
            ValueSort _ -> return ()
            _           -> throwErr "type of 'type' is not a sort"

        let x' = Inf (Var n)
        sTerms . at n ?= (Ann x' t', t'')

    parametricity_ x = do
        startCommand CDefine
        output <- ScriptT $ use sOutput

        if output
        then putPP $ "λ» :parametricity" <+> pppScott (ppp0 x)
        else return ()

        terms <- use sTerms

        let typeCtx  n' = terms ^? ix n' . _2
        let valueCtx n' = maybe (return n') id $ terms ^? ix n' . _1

        let x' = x >>= valueCtx
        (_, t) <- type_ typeCtx x'
        t' <- errorlessValueIntro t

        let triple :: Sym -> (Sym, Sym, Sym)
            triple (Sym s) = (Sym $ s <> "1", Sym $ s <> "2", Sym $ "⟦" <> s <> "⟧")

        let x'' = relationInf triple x
            t'' = relationChk triple (quote_ (t' :: ValueIntro Void s Sym))

        putPP $ pppChar '↪' <+> ppp0 x''
            </> pppChar ':' <+> ppp0 t''

    dumpDefs_ = do
        defs <- use sDefinitions
        for_ (reverse defs) $ \(n, x) ->
            putPP $ ppp0 n <+> pppChar '=' <+> ppp0 x

    example_ x = do
        output <- ScriptT $ use sOutput
        when output $ do
            startCommand CExample
            putPP $ "λ» :example" <+> ppp0 x
            terms <- use sTerms
            let typeCtx  n' = terms ^? ix n' . _2
            let valueCtx n' = maybe (return n') id $ terms ^? ix n' . _1

            (x', t') <- type_ typeCtx (x >>= valueCtx)
            x'' <- errorlessValueIntro x'
            t'' <- errorlessValueIntro t'
            -- quote term back!
            putPP $ pppChar '↪' <+> ppp0 (quote_ (x'' :: ValueIntro Void s Sym))
                </> pppChar ':' <+> ppp0 (quote_ (t'' :: ValueIntro Void s Sym))

pppScott :: PrettyM Doc -> PrettyM Doc
pppScott doc = pppChar '⟦' <> doc <> pppChar '⟧'
    
