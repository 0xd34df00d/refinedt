{-# LANGUAGE DuplicateRecordFields, RecordWildCards #-}

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

data TermT ann
  = TName ann VarName
  | TInteger ann Int
  | TBinOp ann (TermT ann) BinOp (TermT ann)
  | TApp ann (TermT ann) (TermT ann)
  | TIfThenElse { tifeAnn :: ann, tcond :: TermT ann, tthen :: TermT ann, telse :: TermT ann }
  deriving (Eq, Ord, Show)

type Term = TermT ()
type TypedTerm = TermT Ty

annotation :: TermT ann -> ann
annotation (TName ann _) = ann
annotation (TInteger ann _) = ann
annotation (TBinOp ann _ _ _) = ann
annotation (TApp ann _ _) = ann
annotation TIfThenElse { .. } = tifeAnn
