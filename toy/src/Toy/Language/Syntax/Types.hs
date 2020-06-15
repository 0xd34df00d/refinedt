{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable #-}
{-# LANGUAGE RecordWildCards #-}

module Toy.Language.Syntax.Types where

import Data.Data
import Data.Generics.Uniplate.Data
import Data.Maybe

import Toy.Language.Syntax.Common
import Toy.Language.Syntax.Terms

data BaseTy = TBool | TInt | TIntList
  deriving (Eq, Ord, Show, Enum, Bounded, Data)

data AtomicRefinement = AR VarName Term
  deriving (Eq, Ord, Show, Data)

newtype Refinement = Refinement { conjuncts :: [AtomicRefinement] } deriving (Eq, Ord, Show, Data, Semigroup, Monoid)

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

isArrowTy :: Ty -> Bool
isArrowTy TyArrow {} = True
isArrowTy _ = False

isBaseTy :: Ty -> Bool
isBaseTy TyBase {} = True
isBaseTy _ = False

tyRefinement :: Ty -> Maybe Refinement
tyRefinement TyArrow {} = Nothing
tyRefinement (TyBase RefinedBaseTy { .. })
  | baseTyRefinement == trueRefinement = Nothing
  | otherwise = Just baseTyRefinement

tyRefinement' :: Ty -> Refinement
tyRefinement' = fromMaybe trueRefinement . tyRefinement

type TypedTerm = TermT Ty
