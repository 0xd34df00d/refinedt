{-# LANGUAGE DuplicateRecordFields #-}

module Toy.Language.Syntax.Decls where

import Toy.Language.Syntax.Types

data FunSig = FunSig
  { funName :: String
  , funTy :: Ty
  } deriving (Eq, Ord, Show)

data FunDef = FunDef
  { funName :: String
  , funArgs :: [VarName]
  , funBody :: Term
  } deriving (Eq, Ord, Show)

data BinOp = BinOpPlus | BinOpMinus | BinOpGt | BinOpLt deriving (Eq, Ord, Show)

data Term
  = TName VarName
  | TInteger Int
  | TBinOp Term BinOp Term
  | TApp Term Term
  | TIfThenElse { tif :: Term, tthen :: Term, telse :: Term }
  deriving (Eq, Ord, Show)
