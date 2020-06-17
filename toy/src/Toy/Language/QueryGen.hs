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
data RefAnn = RefAnn
  { intrinsic :: Refinement
  , tyAnn :: Ty
  } deriving (Eq, Ord, Show)

type RefAnnTerm = TermT RefAnn
type RefAnnFunDef = FunDefT RefAnn

newtype RefAnnState = RefAnnState { freeRefinementVarsCount :: Int }

type MonadQ m = MonadState RefAnnState m

freshRefVar :: MonadQ m => m VarName
freshRefVar = do
  idx <- gets freeRefinementVarsCount
  modify' $ \st -> st { freeRefinementVarsCount = idx + 1 }
  pure [i|v#{idx}|]

propagateRefinements :: MonadQ m => TypedTerm -> m RefAnnTerm
propagateRefinements (TName ty name) = do
  v' <- freshRefVar
  let refinement = specRefinement v' $ tyRefinement ty
  pure $ TName (RefAnn refinement ty) name
propagateRefinements (TInteger ty n) = do
  v' <- freshRefVar
  let refinement = Refinement v' [AR $ tv v' |=| ti n]
  pure $ TInteger (RefAnn refinement ty) n
propagateRefinements (TBinOp ty t1 op t2) = do
  t1' <- propagateRefinements t1
  t2' <- propagateRefinements t2
  v' <- freshRefVar
  let refinement = Refinement v' [AR $ tv v' |=| TBinOp () (termSubjVarTerm t1') op (termSubjVarTerm t2')]
  pure $ TBinOp (RefAnn refinement ty) t1' op t2'
propagateRefinements (TApp ty fun arg) = do
  fun' <- propagateRefinements fun
  arg' <- propagateRefinements arg
  v' <- freshRefVar
  -- TODO add the symbolic `v' = fun arg` AR?
  let refinement = specRefinement v' $ tyRefinement ty
  pure $ TApp (RefAnn refinement ty) fun' arg'
propagateRefinements TIfThenElse { .. } = do
  tcond' <- propagateRefinements tcond
  tthen' <- propagateRefinements tthen
  telse' <- propagateRefinements telse
  v' <- freshRefVar
  let refinement = Refinement v' [AR $ tv v' |=| TIfThenElse () (termSubjVarTerm tcond')
                                                                (termSubjVarTerm tthen')
                                                                (termSubjVarTerm telse')]
  pure $ TIfThenElse (RefAnn refinement tifeAnn) tcond' tthen' telse'

termSubjVar :: RefAnnTerm -> VarName
termSubjVar = subjectVar . intrinsic . annotation

termSubjVarTerm :: RefAnnTerm -> Term
termSubjVarTerm = TName () . termSubjVar

specRefinement :: VarName -> Maybe Refinement -> Refinement
specRefinement var maybeRef = Refinement var ars
  where
    ars | Just ref <- maybeRef = renameVar' (Proxy :: Proxy ()) (subjectVar ref) var (conjuncts ref)
        | otherwise = []
