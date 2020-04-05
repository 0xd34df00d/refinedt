{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Toy.Language.Solver where

import qualified Data.HashMap.Strict as HM
import Toy.Language.Syntax.Decls

data SolveRes = Sat | Unsat deriving (Eq, Show)

newtype SolveContext = SolveContext
  { visibleSigs :: HM.HashMap String FunSig
  } deriving (Eq, Ord, Show, Semigroup, Monoid)

solve :: SolveContext -> FunSig -> FunDef -> IO SolveRes
solve ctx sig def = undefined
