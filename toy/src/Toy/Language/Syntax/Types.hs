{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RecordWildCards, QuasiQuotes #-}
{-# LANGUAGE FlexibleInstances #-}

module Toy.Language.Syntax.Types where

import Data.Data
import Data.Generics.Uniplate.Data
import Data.List
import Data.String.Interpolate

import Misc.Pretty
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

setTyRefinement :: Ty -> Refinement -> Ty
setTyRefinement t@TyArrow {} _ = t
setTyRefinement (TyBase rbt) ref = TyBase rbt { baseTyRefinement = Just ref }

type TypedTerm = TermT Ty

instance Pretty AtomicRefinement where
  pretty = pretty . getARTerm

instance Pretty [AtomicRefinement] where
  pretty [] = "True"
  pretty ars = intercalate " & " $ pretty <$> ars

instance Pretty Refinement where
  pretty Refinement { .. } = [i|#{getName subjectVar} | #{pretty conjuncts}|]

instance Pretty Ty where
  pretty (TyBase RefinedBaseTy { .. })
    | Just Refinement { .. } <- baseTyRefinement = [i|{ #{getName subjectVar} : #{baseType} | #{pretty conjuncts} } |]
    | otherwise = show baseType
  pretty (TyArrow ArrowTy { .. })
    | Just piVar <- piVarName = [i|(#{getName piVar} : #{parenPretty domTy}) -> #[pretty codTy}|]
    | otherwise = [i|#{parenPretty domTy} -> #[pretty codTy}|]
    where
      parenPretty ty | isArrowTy ty = "(" <> pretty ty <> ")"
                     | otherwise = pretty ty
