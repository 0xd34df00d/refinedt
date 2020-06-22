{-# LANGUAGE RecordWildCards, QuasiQuotes #-}
{-# LANGUAGE DeriveFunctor, DeriveDataTypeable, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications #-}

module Toy.Language.Syntax.Terms where

import Data.Data
import Data.Generics.Uniplate.Data
import Data.Maybe
import Data.String
import Data.String.Interpolate

import Misc.Pretty
import Misc.Util
import Toy.Language.Syntax.Common

data BinOp
  = BinOpPlus | BinOpMinus
  | BinOpLt | BinOpLeq | BinOpEq | BinOpNEq | BinOpGt | BinOpGeq
  deriving (Eq, Ord, Show, Enum, Bounded, Data)

data TermT ann
  = TName { annotation :: ann, _tname :: VarName }
  | TInteger { annotation :: ann, _tint :: Int }
  | TBinOp { annotation :: ann, _tbo1 :: TermT ann, op :: BinOp, _tbo2 :: TermT ann }
  | TApp { annotation :: ann, _fun :: TermT ann, _app :: TermT ann }
  | TIfThenElse { annotation :: ann, tcond :: TermT ann, tthen :: TermT ann, telse :: TermT ann }
  deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)

instance IsString Term where
  fromString = TName () . fromString

type Term = TermT ()

-- this is gonna explode beautifully when we'll have lambda abstractions on term level
renameVar :: forall a. Data a => VarName -> VarName -> TermT a -> TermT a
renameVar what with = transformBi f
  where
    f :: TermT a -> TermT a
    f (TName ann name) | name == what = TName ann with
    f term = term

renameVar' :: forall a from. (Data a, Data from) => Proxy a -> VarName -> VarName -> from -> from
renameVar' _ what with = transformBi (renameVar @a what with)

instance Pretty Term where
  pretty (TName _ x) = getName x
  pretty (TInteger _ n) = show n
  pretty (TBinOp _ t1 op t2) = [i|#{parens $ pretty t1} #{fromJust $ lookup op ps} #{parens $ pretty t2}|]
    where
      ps = [ (BinOpPlus, "+"), (BinOpMinus, "-")
           , (BinOpLt, "<"), (BinOpLeq, "<="), (BinOpEq, "="), (BinOpNEq, "/="), (BinOpGt, ">"), (BinOpGeq, ">=")
           ]
  pretty (TApp _ t1 t2) = [i|#{parens $ pretty t1} #{parens $ pretty t2}|]
  pretty  TIfThenElse { .. } = [i|if #{pretty tcond} then #{pretty tthen} else #{pretty telse}|]
