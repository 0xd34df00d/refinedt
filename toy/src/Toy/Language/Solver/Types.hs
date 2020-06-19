module Toy.Language.Solver.Types where

import Toy.Language.Syntax

-- The intrinsic refinement characterizes the structure of the term and doesn't need to be checked but can be assumed.
data RefAnn = RefAnn
  { intrinsic :: Refinement
  , tyAnn :: Ty
  } deriving (Eq, Ord, Show)

type RefAnnTerm = TermT RefAnn

data Query
  = Refinement :=> Refinement
  | Query :& Query
  deriving (Eq, Ord, Show)

-- The VC proposition `query` is whatever needs to hold for that specific term to type check (not including its subterms).
-- It assumes that `refAnn` holds.
data VCAnnT a = VCAnn
  { query :: Maybe a
  , refAnn :: RefAnn
  } deriving (Eq, Ord, Show)

type QAnn = VCAnnT Query

type QTerm = TermT QAnn
type QFunDef = FunDefT QAnn

termSubjVar :: RefAnnTerm -> VarName
termSubjVar = subjectVar . intrinsic . annotation

termSubjVarTerm :: RefAnnTerm -> Term
termSubjVarTerm = TName () . termSubjVar

