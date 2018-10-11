{-# LANGUAGE OverloadedStrings          #-}
-- | __TBW__ Introduction into examples. And more examples.
module Language.PTS.Examples (
    -- * Identity function
    --
    -- | Identity function is used often to demonstrate polymorphic calculus.
    -- This is not an exception.
    --
    stlcUnitIdentity,
    stlcBoolIdentity,
    polymorphicIdentity,
    systemfIdentity,
    stlcIdentity,
    hindleyMilnerIdentity,
    martinLofIdentity,
    lambdaStarIdentity,
    -- * Church booleans
    churchBooleans,
    -- * Contexts
    emptyCtx,
    basicCtx,
    -- * TODO
    lambdaStarPlus,
    natCtx,
#ifdef LANGUAGE_PTS_HAS_NAT
    natEx,
    natSucc,
    natCtx',
#endif
    -- * Error cases
    --
    -- | In this section we show some errors which can occur.
    --
    scopeError,
    annotationError,
    evaluatorError,
    ) where

import Language.PTS
import Language.PTS.Systems

-------------------------------------------------------------------------------
-- Identity function
-------------------------------------------------------------------------------

-- | In simple typed lambda calculus one have to define separate functions
-- for different types, even they have same shape.
--
-- >>> demo_ basicCtx stlcUnitIdentity
-- λ x → x : Unit → Unit ↪ λ x → x : Unit → Unit
--
-- 'demo_' prints the term, result of evaluation and checked type
--
-- @
-- term ↪ value : type
-- @
--
stlcUnitIdentity :: Term STLC
stlcUnitIdentity =
    lam_ "x" "x"
    -:-
    "Unit" ~> "Unit"

-- | Next we can write identity function for booleans:
--
-- >>> demo_ basicCtx stlcBoolIdentity
-- λ x → x : Bool → Bool ↪ λ x → x : Bool → Bool
--
-- If we would write the type-inferencer for STLC (TODO),
-- it would need to default types for such intristically polymorphic values.
--
-- As this is the first example, let's see evaluator and type-checker in action:
--
-- >>> demo_ basicCtx ("True" :: Term STLC)
-- True ↪ True : Bool
--
-- Next we apply @True@ to the identity function:
--
-- >>> demo_ basicCtx $ stlcBoolIdentity @@ "True"
-- (λ x → x : Bool → Bool) True ↪ True : Bool
--
-- If we apply the value of wrong type, we get an error:
--
-- >>> demo_ basicCtx $ stlcBoolIdentity @@ "TT"
-- error:
-- • Couldn't match expected type Bool with actual type Unit
-- • In the expression: TT
-- • when checking expression
--   (λ x → x : Bool → Bool) TT
--
-- Because the library is based on PTS, we /could/ try to apply a type too,
-- but that's also a type-error:
--
-- >>> demo_ basicCtx $ stlcBoolIdentity @@ "Bool"
-- error:
-- • Couldn't match expected type Bool with actual type ⋆
-- • In the expression: Bool
-- • when checking expression
--   (λ x → x : Bool → Bool) Bool
--
stlcBoolIdentity :: Term STLC
stlcBoolIdentity =
    lam_ "x" "x"
    -:-
    "Bool" ~> "Bool"

-- | Because simply typed lambda calculus is restrictive,
-- we have polymorphic calculi.
--
-- In @language-pts@ we can define the term once and for all specications.
polymorphicIdentity :: Specification s => Term s
polymorphicIdentity =
    lam_ "a" (lam_ "x" "x")
    -:-
    forall_ "a" ("a" ~> "a")

-- | However let's experiment with 'SystemF' first.
--
-- >>> demo_ emptyCtx systemfIdentity
-- λ a x → x : ∀ a → a → a ↪ λ a x → x : ∀ a → a → a
--
-- Note: 'emptyCtx'. We can apply values.
-- When we apply a @Bool@ we get boolean identity function,
-- and further we can apply a Value
--
-- >>> demo_ basicCtx $ systemfIdentity @@ "Bool"
-- (λ a x → x : ∀ a → a → a) Bool ↪ λ x → x : Bool → Bool
--
-- >>> demo_ basicCtx $ systemfIdentity @@ "Bool" @@ "False"
-- (λ a x → x : ∀ a → a → a) Bool False ↪ False : Bool
--
-- As with STLC, we get type-error if we apply value of wrong type:
--
-- >>> demo_ basicCtx $ systemfIdentity @@ "Unit" @@ "False"
-- error:
-- • Couldn't match expected type Unit with actual type Bool
-- • In the expression: False
-- • when checking expression
--   (λ a x → x : ∀ a → a → a) Unit False
--
-- And "sort" error, if we try to apply value directly!
--
-- >>> demo_ basicCtx $ systemfIdentity @@ "False"
-- error:
-- • Couldn't match expected type ⋆ with actual type Bool
-- • In the expression: False
-- • when checking expression
--   (λ a x → x : ∀ a → a → a) False
--
systemfIdentity :: Term SystemF
systemfIdentity = polymorphicIdentity

-- | Note: we can /write/ polymorphic looking identity function in PTS for
-- STLC, but it won't typecheck:
--
-- >>> demo_ emptyCtx stlcIdentity
-- error:
-- • No PTS Rule (□,⋆,-)
-- • when checking expression
--   λ a x → x : ∀ a → a → a
--
stlcIdentity :: Term STLC
stlcIdentity = polymorphicIdentity

-- |
--
-- In Haskell we can apply identity function to itself
--
-- >>> :t id id
-- id id :: a -> a
--
-- GHCs "type-checker" (actually inferrer) infers the following value.
-- Note that all applied types are /simple/, monomorphic types (no 'forall_'):
--
-- >>> demo_ emptyCtx $ lam_ "b" (systemfIdentity @@ ("b" ~> "b") @@ (systemfIdentity @@ "b")) -:- forall_ "b" ("b" ~> "b")
-- λ b → (λ a x → x : ∀ a → a → a)
--           (b → b) ((λ a x → x : ∀ a → a → a) b)
--     : ∀ b → b → b
--     ↪ λ b x → x : ∀ b → b → b
--
-- Alternatively, different value can be inferred (AFAIK that's what Agda would do).
-- Here, as we don't abstract ('lam_'), we don't need annotations, due bi-directional type-checking in @language-pts@!
--
-- >>> demo_ emptyCtx $ systemfIdentity @@ forall_ "b" ("b" ~> "b") @@@ systemfIdentity
-- (λ a x → x : ∀ a → a → a)
--     (∀ b → b → b) (λ a x → x : ∀ a → a → a)
--     ↪ λ a x → x : ∀ b → b → b
--
-- But this won't type-check in predicative System F (= Hindley-Milner, 'HindleyMilner') system:
--
-- >>> demo_ emptyCtx $ hindleyMilnerIdentity @@ forall_ "b" ("b" ~> "b") @@@ hindleyMilnerIdentity
-- error:
-- • Couldn't match expected type M with actual type P
-- • In the expression: ∀ b → b → b
-- • when checking expression
--   (λ a x → x : ∀ a → a → a) (∀ b → b → b)
--   (λ a x → x : ∀ a → a → a) (∀ b → b → b) (λ a x → x : ∀ a → a → a)
--
-- Former is however, ok. Note that we get a polymorphic value!
--
-- >>> demo_ emptyCtx $ Ann (lam_ "b" (hindleyMilnerIdentity @@ ("b" ~> "b") @@ (hindleyMilnerIdentity @@ "b"))) (forall_ "b" ("b" ~> "b"))
-- λ b → (λ a x → x : ∀ a → a → a)
--           (b → b) ((λ a x → x : ∀ a → a → a) b)
--     : ∀ b → b → b
--     ↪ λ b x → x : ∀ b → b → b
--
--
hindleyMilnerIdentity :: Term HindleyMilner
hindleyMilnerIdentity = Ann
    (lam_ "a" $ lam_ "x" "x")   -- term
    (forall_ "a" $ "a" ~> "a")  -- type

martinLofIdentity :: Term MartinLof
martinLofIdentity = Ann
    (lam_ "a" $ lam_ "x" "x")   -- term
    (forall_ "a" $ "a" ~> "a")  -- type

lambdaStarIdentity :: Term LambdaStar
lambdaStarIdentity = polymorphicIdentity

-------------------------------------------------------------------------------
-- Booleans
-------------------------------------------------------------------------------

-- | 'SystemF' is powerful enough to define Church Booleans.
--
-- >>> runLoud $ spec_ SysFStar >> churchBooleans
-- λ» :define Bool : ⋆ = ∀ r → r → r → r
-- λ» :define True : Bool = λ r t f → t
-- λ» :define False : Bool = λ r t f → f
-- |
-- -- Bool values are itself an if statement
-- λ» :define not : Bool → Bool = λ x → x Bool False True
-- λ» :define and : Bool → Bool → Bool = λ x y → x Bool y False
-- |
-- -- One have to look carefully to distinguish the results :)
-- λ» :example and True True
-- ↪ λ r t f → t : ∀ r → r → r → r
-- |
-- λ» :example and True False
-- ↪ λ r t f → f : ∀ r → r → r → r
-- |
-- λ» :example and False True
-- ↪ λ r t f → f : ∀ r → r → r → r
-- |
-- ∎
--
churchBooleans :: Script s m => m ()
churchBooleans = do
    define_ "Bool"
        $$ sort_ typeSort
        $$ forall_ "r" ("r" ~> "r" ~> "r")

    define_ "True"
        $$ "Bool"
        $$ lams_ ["r", "t", "f"] "t"

    define_ "False"
        $$ "Bool"
        $$ lams_ ["r", "t", "f"] "f"

    comment_ "Bool values are itself an if statement"
    define_ "not"
        $$ "Bool" ~> "Bool"
        $$ lam_ "x" ("x" @@ "Bool" @@ "False" @@ "True")

    define_ "and"
        $$ "Bool" ~> "Bool" ~> "Bool"
        $$ lams_ ["x", "y"] ("x" @@ "Bool" @@ "y" @@ "False")

    comment_ "One have to look carefully to distinguish the results :)"
    example_ $ "and" @@ "True"  @@ "True"
    example_ $ "and" @@ "True"  @@ "False"
    example_ $ "and" @@ "False" @@ "True"

-------------------------------------------------------------------------------
-- Basic types
-------------------------------------------------------------------------------

emptyCtx :: a -> Maybe (Value s)
emptyCtx = const Nothing

basicCtx :: Specification s => Sym -> Maybe (Value s)
basicCtx "Unit"  = Just (ValueSort typeSort)
basicCtx "Bool"  = Just (ValueSort typeSort)
basicCtx "True"  = Just "Bool"
basicCtx "False" = Just "Bool"
basicCtx "TT"    = Just "Unit"
basicCtx _       = Nothing

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


natEx :: Value LambdaStar
natEx = (lam_ "x" $ ValueCoerce $ ValueNatElim (lam_ "?" $ ValueNat) ValueNatZ (lams_ ["k","x"] $ ValueNatS (ValueNatS "x")) "x") `valueApp` ValueNatS ValueNatZ

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
-- Error cases
-------------------------------------------------------------------------------

-- |
--
-- >>> demo_ basicCtx ("Boo" :: Term LambdaStar)
-- error:
-- • Variable not in scope Boo
scopeError :: ()
scopeError = ()

-- |
--
-- >>> demo_ basicCtx (lam_ "x" "x" -:- "Bool" :: Term STLC)
-- error:
-- • The lambda expression λ x → x doesn't have a Pi-type
-- • Annotated with Bool
-- • when checking expression
--   λ x → x : Bool
--
annotationError :: ()
annotationError = ()

-- |
--
-- >>> demo_ basicCtx ("True" @@ "False" :: Term LambdaStar)
-- error:
-- • Couldn't match actual type Bool with a function type
-- • In the application of True
-- • to the value False
-- • when checking expression
--   True False
--
-- If we try to apply variable to variable values, it's ok however.
-- We can be weird, so @"True"@ is actually a function:
--
-- >>> prettyPut ("True" @@ "False" :: Value LambdaStar)
-- True False
--
-- Yet, if we apply to a sort, or Pi-type or something else obviously incorrect:
-- value will fail:
--
-- >>> prettyPut (sort_ LambdaStar `valueApp` "False" :: Value LambdaStar)
-- panic: Trying to apply not-a-lambda ⋆
--
-- We don't print a value we try to apply, because it's still not evaluated.
-- (often some variable in a scope).
--
evaluatorError :: ()
evaluatorError =  ()

-------------------------------------------------------------------------------
-- Doctest
-------------------------------------------------------------------------------

-- $setup
-- >>> :set -XOverloadedStrings -XTypeApplications
-- >>> import Language.PTS.Pretty
