{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RecordWildCards #-}

module Toy.Language.Syntax.Types where

import Data.Data
import Data.Generics.Uniplate.Data

import Toy.Language.Syntax.Common
import Toy.Language.Syntax.Terms

data BaseTy = TBool | TInt | TIntList
  deriving (Eq, Ord, Show, Enum, Bounded, Data)

newtype AtomicRefinement = AR { getARTerm :: Term }
  deriving (Eq, Ord, Show, Data)

data Refinement = Refinement
  { subjectVar :: VarName
  , conjuncts :: [AtomicRefinement]
  } deriving (Eq, Ord, Show, Data)

trueRefinement :: Maybe Refinement
trueRefinement = Nothing

data RefinedBaseTy = RefinedBaseTy
 { baseType :: BaseTy
 , baseTyRefinement :: Maybe Refinement
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

isArrowTy :: Ty -> Bool
isArrowTy TyArrow {} = True
isArrowTy _ = False

isBaseTy :: Ty -> Bool
isBaseTy TyBase {} = True
isBaseTy _ = False

tyRefinement :: Ty -> Maybe Refinement
tyRefinement TyArrow {} = Nothing
tyRefinement (TyBase RefinedBaseTy { .. }) = baseTyRefinement

type TypedTerm = TermT Ty
