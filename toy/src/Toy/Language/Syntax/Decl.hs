{-# LANGUAGE DuplicateRecordFields #-}

module Toy.Language.Syntax.Decl where

import Toy.Language.Syntax.Types

data FunDecl = FunDecl
  { funName :: String
  , funTy :: Ty
  } deriving (Eq, Ord, Show)

data FunDef = FunDef
  { funName :: String
  , funArgs :: [VarName]
  , funBody :: Term
  } deriving (Eq, Ord, Show)

data Op = OpPlus | OpMinus | OpGt | OpLt deriving (Eq, Ord, Show)

data Term
  = TName VarName
  | TInteger Int
  | TOperator Op
  | TApp Term Term
  | TIfThenElse { tif :: Term, tthen :: Term, telse :: Term }
  deriving (Eq, Ord, Show)
