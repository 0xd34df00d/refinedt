{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE QuasiQuotes #-}

module Toy.Language.Solver.Types where

import Data.Maybe
import Data.String.Interpolate
import Z3.Monad(Result(..))

import Misc.Pretty
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

instance Pretty Query where
  pretty (r1 :=> r2) = [i|(#{pretty r1}) :=> (#{pretty r2})|]
  pretty (q1 :& q2) = pretty q1 <> " & " <> pretty q2

-- The VC proposition `query` is whatever needs to hold for that specific term to type check (not including its subterms).
-- It assumes that `refAnn` holds.
data VCAnnT a = VCAnn
  { query :: Maybe a
  , refAnn :: RefAnn
  } deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type QAnn = VCAnnT Query

type QTerm = TermT QAnn
type QFunDef = FunDefT QAnn

termSubjVar :: RefAnnTerm -> VarName
termSubjVar = subjectVar . intrinsic . annotation

termSubjVarTerm :: RefAnnTerm -> Term
termSubjVarTerm = TName () . termSubjVar

-- A term annotated with a VC-related info
type VCTerm a = TermT (VCAnnT a)

onVCTerm :: Monad m => (a -> m b) -> VCTerm a -> m (VCTerm b)
onVCTerm f term = traverse sequence $ fmap f <$> term

setQuery :: a -> VCTerm a -> VCTerm a
setQuery query term = term { annotation = (annotation term) { query = Just query }}

data SolveRes = Correct | Wrong deriving (Eq, Show)

convertZ3Result :: Result -> SolveRes
convertZ3Result Sat = Correct
convertZ3Result Unsat = Wrong
convertZ3Result Undef = Wrong -- TODO

isAllCorrect :: Foldable t => t (Maybe SolveRes) -> SolveRes
isAllCorrect cont | all ((== Correct) . fromMaybe Correct) cont = Correct
                  | otherwise = Wrong
