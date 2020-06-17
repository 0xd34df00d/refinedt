{-# LANGUAGE QuasiQuotes, RecordWildCards #-}
{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}

module Toy.Language.QueryGen where

import Control.Monad.State.Strict
import Data.Proxy
import Data.String.Interpolate.IsString

import Toy.Language.Syntax.Common
import Toy.Language.Syntax.Decls
import Toy.Language.Syntax.Terms
import Toy.Language.Syntax.Terms.Sugar
import Toy.Language.Syntax.Types

-- The intrinsic refinement characterizes the structure of the term and doesn't need to be checked but can be assumed.
-- The VC proposition is whatever needs to hold for that specific term to type check (not including its subterms).
data QAnnotation = QAnnotation
  { intrinsic :: Refinement
  , tyAnn :: Ty
  } deriving (Eq, Ord, Show)

type QTerm = TermT QAnnotation
type QFunDef = FunDefT QAnnotation

data QState = QState
  { freeRefinementVarsCount :: Int
  }

type MonadQ m = MonadState QState m

freshRefVar :: MonadQ m => m VarName
freshRefVar = do
  idx <- gets freeRefinementVarsCount
  modify' $ \st -> st { freeRefinementVarsCount = idx + 1 }
  pure [i|v#{idx}|]

genQueries :: MonadQ m => TypedTerm -> m QTerm
genQueries (TName ty name) = do
  v' <- freshRefVar
  let refinement = specRefinement v' $ tyRefinement ty
  pure $ TName (QAnnotation refinement ty) name
genQueries (TInteger ty n) = do
  v' <- freshRefVar
  let refinement = Refinement v' [AR $ tv v' |=| ti n]
  pure $ TInteger (QAnnotation refinement ty) n
genQueries (TBinOp ty t1 op t2) = do
  t1' <- genQueries t1
  t2' <- genQueries t2
  v' <- freshRefVar
  let refinement = Refinement v' [AR $ tv v' |=| TBinOp () (termSubjVarTerm t1') op (termSubjVarTerm t2')]
  pure $ TBinOp (QAnnotation refinement ty) t1' op t2'
genQueries (TApp ty fun arg) = do
  fun' <- genQueries fun
  arg' <- genQueries arg
  v' <- freshRefVar
  let refinement = specRefinement v' $ tyRefinement ty
  pure $ TApp (QAnnotation refinement ty) fun' arg'
genQueries TIfThenElse { .. } = do
  tcond' <- genQueries tcond
  tthen' <- genQueries tthen
  telse' <- genQueries telse
  v' <- freshRefVar
  let refinement = Refinement v' [AR $ tv v' |=| TIfThenElse () (termSubjVarTerm tcond')
                                                                (termSubjVarTerm tthen')
                                                                (termSubjVarTerm telse')]
  pure $ TIfThenElse (QAnnotation refinement tifeAnn) tcond' tthen' telse'

termSubjVar :: QTerm -> VarName
termSubjVar = subjectVar . intrinsic . annotation

termSubjVarTerm :: QTerm -> Term
termSubjVarTerm = TName () . termSubjVar

specRefinement :: VarName -> Maybe Refinement -> Refinement
specRefinement var maybeRef = Refinement var ars
  where
    ars | Just ref <- maybeRef = renameVar' (Proxy :: Proxy ()) (subjectVar ref) var (conjuncts ref)
        | otherwise = []
