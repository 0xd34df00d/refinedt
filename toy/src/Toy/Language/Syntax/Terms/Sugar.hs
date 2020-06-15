{-# LANGUAGE OverloadedStrings #-}

module Toy.Language.Syntax.Terms.Sugar where

import Data.String

import Toy.Language.Syntax.Common
import Toy.Language.Syntax.Terms

v :: IsString s => s
v = "v"

ti :: Int -> Term
ti = TInteger ()

tv :: VarName -> Term
tv = TName ()

(|=|), (|+|), (|-|), (|>|), (|<|), (|>=|), (|<=|) :: Term -> Term -> Term
t1 |=| t2 = TBinOp () t1 BinOpEq t2
t1 |+| t2 = TBinOp () t1 BinOpPlus t2
t1 |-| t2 = TBinOp () t1 BinOpMinus t2
t1 |>| t2 = TBinOp () t1 BinOpGt t2
t1 |<| t2 = TBinOp () t1 BinOpLt t2
t1 |>=| t2 = TBinOp () t1 BinOpGeq t2
t1 |<=| t2 = TBinOp () t1 BinOpLeq t2

len :: String -> Term
len x = TApp () "len" (fromString x)