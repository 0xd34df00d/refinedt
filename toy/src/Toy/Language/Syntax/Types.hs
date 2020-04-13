{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Toy.Language.Syntax.Types where

import Data.Data
import Data.Generics.Uniplate.Data
import Data.Hashable
import Data.String

newtype VarName = VarName { getName :: String } deriving (Eq, Ord, Show, IsString, Hashable, Data)

data BaseTy = TBool | TInt | TIntList
  deriving (Eq, Ord, Show, Enum, Bounded, Data)

-- Following liquid-types-08 paper, chapter 5

data RefinementOp = ROpLt | ROpLeq | ROpEq | ROpNEq | ROpGt | ROpGeq deriving (Eq, Ord, Show, Enum, Bounded, Data)

data RefinementArg = RArgZero | RArgVar VarName | RArgVarLen VarName deriving (Eq, Ord, Show, Data)

data AtomicRefinement = AR RefinementOp RefinementArg
  deriving (Eq, Ord, Show, Data)

newtype Refinement = Refinement { conjuncts :: [AtomicRefinement] } deriving (Eq, Ord, Show, Data)

trueRefinement :: Refinement
trueRefinement = Refinement []

data RefinedBaseTy = RefinedBaseTy
 { baseType :: BaseTy
 , baseTyRefinement :: Refinement
 } deriving (Eq, Ord, Show, Data)

data ArrowTy = ArrowTy
 { piVarName :: Maybe VarName
 , domTy :: Ty
 , codTy :: Ty
 } deriving (Eq, Ord, Show, Data)

data Ty
  = TyArrow ArrowTy
  | TyBase RefinedBaseTy
  deriving (Eq, Ord, Show, Data)

stripRefinements :: Ty -> Ty
stripRefinements = transformBi $ const trueRefinement
