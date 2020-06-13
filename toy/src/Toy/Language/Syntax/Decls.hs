{-# LANGUAGE DuplicateRecordFields, RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}

module Toy.Language.Syntax.Decls where

import Toy.Language.Syntax.Types

data FunSig = FunSig
  { funName :: String
  , funTy :: Ty
  } deriving (Eq, Ord, Show)

data FunDefT a = FunDef
  { funName :: String
  , funArgs :: [VarName]
  , funBody :: TermT a
  } deriving (Eq, Ord, Show, Functor)

data BinOp = BinOpPlus | BinOpMinus | BinOpGt | BinOpLt deriving (Eq, Ord, Show)

data TermT ann
  = TName ann VarName
  | TInteger ann Int
  | TBinOp ann (TermT ann) BinOp (TermT ann)
  | TApp ann (TermT ann) (TermT ann)
  | TIfThenElse { tifeAnn :: ann, tcond :: TermT ann, tthen :: TermT ann, telse :: TermT ann }
  deriving (Eq, Ord, Show, Functor)

type Term = TermT ()
type TypedTerm = TermT Ty

type FunDef = FunDefT ()
type TypedFunDef = FunDefT Ty

data DeclT a = Decl
  { declSig :: FunSig
  , declDef :: Maybe (FunDefT a)
  } deriving (Eq, Ord, Show, Functor)

type Decl = DeclT ()

annotation :: TermT ann -> ann
annotation (TName ann _) = ann
annotation (TInteger ann _) = ann
annotation (TBinOp ann _ _ _) = ann
annotation (TApp ann _ _) = ann
annotation TIfThenElse { .. } = tifeAnn
