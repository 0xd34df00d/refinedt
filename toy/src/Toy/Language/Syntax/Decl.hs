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
  , funBody :: Expr
  } deriving (Eq, Ord, Show)

data Op = OpPlus | OpMinus | OpGt | OpLt deriving (Eq, Ord, Show)

data Expr
  = EName VarName
  | EInt Int
  | EOperator Op
  | EApp Expr Expr
  | EIfThenElse { eif :: Expr, ethen :: Expr, eelse :: Expr }
  deriving (Eq, Ord, Show)
