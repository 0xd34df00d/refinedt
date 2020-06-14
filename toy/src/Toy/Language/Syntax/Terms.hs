{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}

module Toy.Language.Syntax.Terms where

import Toy.Language.Syntax.Common

data BinOp
  = BinOpPlus | BinOpMinus
  | BinOpLt | BinOpLeq | BinOpEq | BinOpNEq | BinOpGt | BinOpGeq
  deriving (Eq, Ord, Show)

data TermT ann
  = TName ann VarName
  | TInteger ann Int
  | TBinOp ann (TermT ann) BinOp (TermT ann)
  | TApp ann (TermT ann) (TermT ann)
  | TIfThenElse { tifeAnn :: ann, tcond :: TermT ann, tthen :: TermT ann, telse :: TermT ann }
  deriving (Eq, Ord, Show, Functor)

type Term = TermT ()
type TypedTerm = TermT Ty

annotation :: TermT ann -> ann
annotation (TName ann _) = ann
annotation (TInteger ann _) = ann
annotation (TBinOp ann _ _ _) = ann
annotation (TApp ann _ _) = ann
annotation TIfThenElse { .. } = tifeAnn
