{-# LANGUAGE OverloadedStrings #-}
module Language.PTS.Examples.Contexts (
    emptyCtx,
    basicCtx,
    ) where

import Language.PTS

emptyCtx :: a -> Maybe (Value s)
emptyCtx = const Nothing

basicCtx :: Specification s => Sym -> Maybe (Value s)
basicCtx "Unit"  = Just (ValueSort typeSort)
basicCtx "Bool"  = Just (ValueSort typeSort)
basicCtx "True"  = Just "Bool"
basicCtx "False" = Just "Bool"
basicCtx "TT"    = Just "Unit"
basicCtx _       = Nothing
