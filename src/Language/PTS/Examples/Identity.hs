{-# LANGUAGE OverloadedStrings #-}
-- | Identity function is used often to demonstrate polymorphic calculus.
-- This is not an exception.
module Language.PTS.Examples.Identity (
    stlcUnitIdentity,
    stlcBoolIdentity,
    polymorphicIdentity,
    systemfIdentity,
    stlcIdentity,
    hindleyMilnerIdentity,
    martinLofIdentity,
    lambdaStarIdentity,
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


-- $setup
-- >>> :set -XOverloadedStrings -XTypeApplications
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Systems
-- >>> import Language.PTS.Examples.Contexts
