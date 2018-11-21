{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Data.ByteString.Lazy.UTF8 (fromString)
import Test.Tasty                (defaultMain, testGroup)
import Test.Tasty.Golden         (goldenVsString)

import Language.PTS.Examples
import Language.PTS.Script
import Language.PTS.Systems

main :: IO ()
main = defaultMain $ testGroup "Girard's Paradox"
    [ goldenVsString "HOL" "fixtures/hurkens-hol.txt" $ return $ fromString $
        runString $ spec_ HOLStar >> hurkensScript'
    , goldenVsString "System  U" "fixtures/hurkens-system-u.txt" $ return $ fromString $
        runString $ spec_ SysUStar >> hurkensScript'
    , goldenVsString "System ⋆" "fixtures/hurkens-lambda-star.txt" $ return $ fromString $
        runString $ spec_ LambdaStar >> hurkensScript'
    ]
  where
    hurkensScript' :: Script s m => m ()
    hurkensScript' = do
        hurkensScript
        section_ "Extras"
        example_ "H"
        example_ "negH"
