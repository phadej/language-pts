{-# LANGUAGE OverloadedStrings #-}
module Language.PTS.Examples.Postulates (
    postulatesScript,
    parametricityScript,
) where

import Language.PTS

-- $setup
-- >>> :seti -XOverloadedStrings -XTypeApplications
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Systems

-------------------------------------------------------------------------------
-- Postulates
-------------------------------------------------------------------------------

-- |
--
-- >>> runLoud $ spec_ SysFStar >> postulatesScript
-- -- 1. Postulate examples
-- ------------------------
-- --
-- λ» :postulate A : ⋆
-- --
-- λ» :example A
-- ↪ A : ⋆
-- --
-- λ» :postulate f : A → A
-- λ» :postulate x : A
-- --
-- λ» :example f x
-- ↪ f x : A
-- ∎
--
postulatesScript :: Script s m => m ()
postulatesScript = do
    section_ "Postulate examples"

    postulate_ "A" (sort_ typeSort)
    example_ "A"

    postulate_ "f" $ "A" ~> "A"
    postulate_ "x" "A"

    example_ $ "f" @@ "x"

-------------------------------------------------------------------------------
-- Parametricity
-------------------------------------------------------------------------------

-- |
--
-- >>> runLoud $ spec_ LambdaStar >> parametricityScript
parametricityScript :: (ReflectiveSpecification s, Script s m) => m ()
parametricityScript = do
    section_ "Sorts"

    parametricity_
        $$ sort_ typeSort

    parametricity_ 
        $$ pi_ "x" (sort_ typeSort) (sort_ typeSort)

    postulate_ "A" (sort_ typeSort)
    postulate_ "B" ("A" ~> sort_ typeSort)

    parametricity_ $$ pi_ "x" "A" ("B" @@ "x")

