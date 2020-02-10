module Toy.Language.Types where

newtype VarName = VarName { getName :: String } deriving (Eq, Ord, Show)

data BaseTy = TBool | TInt
  deriving (Eq, Ord, Show)

-- Following liquid-types-08 paper, chapter 5

data RefinementOp = ROpLe | ROpLeq | ROpEq | ROpNEq | ROpGe | ROpGeq deriving (Eq, Ord, Show)

data RefinementArg = RArgZero | RArgVar VarName | RArgVarLen VarName deriving (Eq, Ord, Show)

data BaseRefinement = BR RefinementOp RefinementArg
  deriving (Eq, Ord, Show)

data Refinement
  = RTrue
  | RAnd Refinement Refinement
  | RBase BaseRefinement
  deriving (Eq, Ord, Show)

data RefinedBaseTy = RefinedBaseTy
 { baseType :: BaseTy
 , refinement :: Refinement
 } deriving (Eq, Ord, Show)
 
data Ty
  = TyArrow (Maybe VarName) Ty Ty
  | TyBase RefinedBaseTy
  deriving (Eq, Ord, Show)
