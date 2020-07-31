{-# LANGUAGE OverloadedStrings #-}
module Language.PTS.Examples.Postulates (
    postulatesScript,
) where

import Language.PTS

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

-- $setup
-- >>> :seti -XOverloadedStrings -XTypeApplications
-- >>> import Language.PTS.Pretty
-- >>> import Language.PTS.Systems
