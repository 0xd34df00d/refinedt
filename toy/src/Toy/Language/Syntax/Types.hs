{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Toy.Language.Syntax.Types where

import Data.String

newtype VarName = VarName { getName :: String } deriving (Eq, Ord, Show, IsString)

data BaseTy = TBool | TInt | TIntList
  deriving (Eq, Ord, Show)

-- Following liquid-types-08 paper, chapter 5

data RefinementOp = ROpLe | ROpLeq | ROpEq | ROpNEq | ROpGe | ROpGeq deriving (Eq, Ord, Show)

data RefinementArg = RArgZero | RArgVar VarName | RArgVarLen VarName deriving (Eq, Ord, Show)

data AtomicRefinement = AR RefinementOp RefinementArg
  deriving (Eq, Ord, Show)

newtype Refinement = Refinement { conjuncts :: [AtomicRefinement] } deriving (Eq, Ord, Show)

trueRefinement :: Refinement
trueRefinement = Refinement []

data RefinedBaseTy = RefinedBaseTy
 { baseType :: BaseTy
 , baseTyRefinement :: Refinement
 } deriving (Eq, Ord, Show)

data ArrowTy = ArrowTy
 { piVarName :: Maybe VarName
 , domTy :: Ty
 , codTy :: Ty
 } deriving (Eq, Ord, Show)

data Ty
  = TyArrow ArrowTy
  | TyBase RefinedBaseTy
  deriving (Eq, Ord, Show)
