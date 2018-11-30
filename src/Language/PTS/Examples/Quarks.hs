#ifdef LANGUAGE_PTS_HAS_QUARKS
#ifdef LANGUAGE_PTS_HAS_PROP
#define QUARKS_EXAMPLES
#endif
#endif

#ifdef QUARKS_EXAMPLES
{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, FlexibleContexts #-}
#endif
module Language.PTS.Examples.Quarks (
#ifdef QUARKS_EXAMPLES
    quarkSyntaxScript,
    monadScript,
#endif
    ) where

#ifdef QUARKS_EXAMPLES
import Language.PTS
import Language.PTS.Bound

import qualified Data.Set as Set
import qualified Data.Map as Map

-- Move: to Smart
hadron_ :: [Sym] -> TermInf s a
hadron_ = Hadron . Set.fromList

quarkElim_ :: Convert TermInf v => Sym -> TermInf s Sym -> TermChk s Sym -> [(Sym, TermChk s Sym)] -> v s Sym
quarkElim_ x@"_" p q qs = convert $ QuarkElim (IrrSym x) (liftH p)           (Map.fromList qs) q
quarkElim_ x     p q qs = convert $ QuarkElim (IrrSym x) (abstract1HSym x p) (Map.fromList qs) q

-- |
--
-- >>> runLoud $ spec_ CoCStar >> quarkSyntaxScript
-- -- Using quarks we can form a variant of Booleans
-- --
-- -- 1. Type
-- ----------
-- --
-- λ» :define Boolean : ⋆ = {:false :true}
-- --
-- -- 2. Constructors
-- ------------------
-- --
-- λ» :define True : Boolean = :true
-- λ» :define False : Boolean = :false
-- --
-- -- 3. Elimination
-- -----------------
-- --
-- λ» :define if
-- : ∀ r → Boolean → r → r → r
-- = λ r b t f → ℚ-elim (λ _ → r) b {:false → f;:true → t}
-- --
-- -- 4. Examples
-- --------------
-- --
-- λ» :define not : Boolean → Boolean
--                = λ b → if Boolean b False True
-- --
-- λ» :example not
-- ↪ λ b → ℚ-elim (λ _ → {:false :true}) b {:false → :true
--                                         ;:true → :false}
-- : {:false :true} → {:false :true}
-- --
-- λ» :example not True
-- ↪ :false : {:false :true}
-- --
-- λ» :example not False
-- ↪ :true : {:false :true}
-- ∎
--
quarkSyntaxScript :: forall s m. Script s m => m ()
quarkSyntaxScript = do
    comment_ "Using quarks we can form a variant of Booleans"

    section_ "Type"

    define_ "Boolean"
        $$ sort_ typeSort
        $$ Inf (hadron_ ["true", "false"])

    section_ "Constructors"

    define_ "True"
        $$ "Boolean"
        $$ Quark "true"

    define_ "False"
        $$ "Boolean"
        $$ Quark "false"

    section_ "Elimination"

    define_ "if"
        $$ forall_ "r" ("Boolean" ~> "r" ~> "r" ~> "r")
        $$ lams_ ["r","b","t","f"]
            (quarkElim_ "_" "r" "b"
                [ "true"  .= "t"
                , "false" .= "f"
                ])

    section_ "Examples"

    define_ "not"
        $$ "Boolean" ~> "Boolean"
        $$ lam_ "b" ("if" @@ "Boolean" @@ "b" @@ "False" @@ "True")

    example_ "not"
    example_ $ "not" @@ "True"
    example_ $ "not" @@ "False"

-- | This script demonstrates usage of quarks for making records,
-- and defines a 'Monad' using @RankNTypes@ approach.
--
-- >>> runLoud $ spec_ CoCStar >> monadScript
-- -- 1. Class
-- -----------
-- --
-- λ» :define MonadMethods = {:fmap :join :pure}
-- λ» :define Monad'
-- : (⋆ → ⋆) → MonadMethods → ⋆
-- = λ M q → ℚ-elim (λ _ → ⋆)
--                  q
--                  {:fmap → (∀ A → ∀ B → (A → B) → M A → M B)
--                  ;:join → (∀ A → M (M A) → M A)
--                  ;:pure → (∀ A → A → M A)}
-- λ» :define Monad
-- : (⋆ → ⋆) → ⋆ = λ M → ∏ (q : MonadMethods) → Monad' M q
-- --
-- -- 2. Identity
-- --------------
-- --
-- λ» :define Identity : ⋆ → ⋆ = λ A → A
-- λ» :define MonadIdentity
-- : Monad Identity = λ q → ℚ-elim (λ q₁ → Monad' Identity q₁)
--                                 q
--                                 {:fmap → (λ _ _ f → f)
--                                 ;:join → (λ _ x → x)
--                                 ;:pure → (λ _ x → x)}
-- --
-- -- 3. Proxy
-- -----------
-- --
-- λ» :define Proxy : ⋆ → ⋆ = λ _ → ⊤
-- λ» :define MonadProxy
-- : Monad Proxy = λ q → ℚ-elim (λ q₁ → Monad' Proxy q₁)
--                              q
--                              {:fmap → (λ _ _ _ _ → I)
--                              ;:join → (λ _ _ → I)
--                              ;:pure → (λ _ _ → I)}
-- --
-- -- 4. Reader
-- ------------
-- --
-- λ» :define Reader : ⋆ → ⋆ → ⋆ = λ E A → E → A
-- λ» :define MonadReader
-- : ∀ E → Monad (Reader E)
-- = λ E q → ℚ-elim (λ q₁ → Monad' (Reader E) q₁)
--                  q
--                  {:fmap → (λ A B ab ea e → ab (ea e))
--                  ;:join → (λ A eea e → eea e e)
--                  ;:pure → (λ A a e → a)}
-- --
-- -- 5. Polymorphic usage
-- -----------------------
-- --
-- λ» :define void
-- : ∏ (M : (⋆ → ⋆)) → Monad M → ∀ A → M A → M ⊤
-- = λ M $M A m → $M :fmap A ⊤ (λ _ → I) m
-- --
-- λ» :example void Identity
--                  MonadIdentity
--                  (∀ X → X → X)
--                  (λ X x → x)
-- ↪ I : ⊤
-- --
-- λ» :define env = {:bar :foo}
-- --
-- λ» :example void (Reader env) (MonadReader env) env (λ e →
--                                                          e)
-- ↪ λ e → I : {:bar :foo} → ⊤
-- ∎
--
monadScript :: forall s m. Script s m => m ()
monadScript = do
    section_ "Class"

    defineInf_ "MonadMethods" $ hadron_ ["pure" , "fmap", "join"]

    define_ "Monad'"
        $$ (sort_ typeSort ~> sort_ typeSort) ~> "MonadMethods" ~> sort_ typeSort
        $$ lams_ ["M","q"] (quarkElim_ "_" (sort_ typeSort) "q"
            [ "pure" .= forall_ "A" ("A" ~> "M" @@ "A")
            , "fmap" .= foralls_ ["A","B"] (("A" ~> "B") ~> "M" @@ "A" ~> "M" @@ "B")
            , "join" .= forall_ "A" ("M" @@ ("M" @@ "A") ~> "M" @@ "A")
            ])

    define_ "Monad"
        $$ (sort_ typeSort ~> sort_ typeSort) ~> sort_ typeSort
        $$ lam_ "M" (pi_ "q" "MonadMethods" $ "Monad'" @@ "M" @@ "q")

    section_ "Identity"

    define_ "Identity"
        $$ sort_ typeSort ~> sort_ typeSort
        $$ lam_ "A" "A"

    define_ "MonadIdentity"
        $$ "Monad" @@ "Identity"
        $$ lam_ "q" (quarkElim_ "q" ("Monad'" @@ "Identity" @@ "q") "q"
            [ "pure" .= lams_ ["_","x"] "x"
            , "fmap" .= lams_ ["_","_","f"] "f"
            , "join" .= lams_ ["_","x"] "x"
            ])

    section_ "Proxy"

    define_ "Proxy"
        $$ sort_ typeSort ~> sort_ typeSort
        $$ lam_ "_" (Inf Unit)

    define_ "MonadProxy"
        $$ "Monad" @@ "Proxy"
        $$ lam_ "q" (quarkElim_ "q" ("Monad'" @@ "Proxy" @@ "q") "q"
            [ "pure" .= lams_ ["_","_"] (Inf I)
            , "fmap" .= lams_ ["_","_","_","_"] (Inf I)
            , "join" .= lams_ ["_","_"] (Inf I)
            ])

    section_ "Reader"
    
    define_ "Reader"
        $$ sort_ typeSort ~> sort_ typeSort ~> sort_ typeSort
        $$ lams_ ["E","A"] ("E" ~> "A")

    define_ "MonadReader"
        $$ forall_ "E" ("Monad" @@ ("Reader" @@ "E"))
        $$ lams_ ["E","q"] (quarkElim_ "q" ("Monad'" @@ ("Reader" @@ "E") @@ "q") "q"
            [ "pure" .= lams_ ["A","a","e"] "a"
            , "fmap" .= lams_ ["A","B","ab","ea","e"] ("ab" @@ ("ea" @@ "e"))
            , "join" .= lams_ ["A","eea","e"] ("eea" @@ "e" @@ "e")
            ])

    section_ "Polymorphic usage"

    define_ "void"
        $$ pi_ "M" (sort_ typeSort ~> sort_ typeSort) ("Monad" @@ "M" ~> forall_ "A" ("M" @@ "A" ~> "M" @@@ Unit))
        $$ lams_ ["M","$M","A","m"] ("$M" @@ Quark "fmap" @@ "A" @@@ Unit @@ lam_ "_" (Inf I) @@ "m")

    example_ $ "void" @@ "Identity" @@ "MonadIdentity" @@ forall_ "X" ("X" ~> "X") @@ lams_ ["X","x"] "x"

    defineInf_ "env" (hadron_ ["foo", "bar"])
    example_ $ "void" @@ ("Reader" @@ "env") @@ ("MonadReader" @@ "env") @@ "env" @@ lam_ "e" "e"

-- $setup
-- >>> :seti -XOverloadedStrings -XTypeApplications
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Systems
#endif
