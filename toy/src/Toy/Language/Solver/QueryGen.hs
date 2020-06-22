{-# LANGUAGE QuasiQuotes, RecordWildCards #-}
{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}

module Toy.Language.Solver.QueryGen
( genQueriesTerm
, genQueriesFunDef
) where

import Control.Monad.State.Strict
import Data.Proxy
import Data.String.Interpolate.IsString

import Toy.Language.EnvironmentUtils
import Toy.Language.Solver.Types
import Toy.Language.Syntax
import Toy.Language.Syntax.Terms.Sugar

genQueriesTerm :: FunSig -> TypedTerm -> QTerm
genQueriesTerm sig t = evalState (propagateRefinements t >>= genQueries >>= addRetTypeQuery sig) (RefAnnState 0)

addRetTypeQuery :: MonadQ m => FunSig -> QTerm -> m QTerm
addRetTypeQuery funSig term = do
  query <- actual <: expected
  pure $ setQuery query term
  where
    expected = TyBase $ retType funSig
    actual = tyAnn $ refAnn $ annotation term

genQueriesFunDef :: FunSig -> TypedFunDef -> QFunDef
genQueriesFunDef = onFunBody . genQueriesTerm

newtype RefAnnState = RefAnnState { freeRefinementVarsCount :: Int }

type MonadQ m = MonadState RefAnnState m

propagateRefinements :: MonadQ m => TypedTerm -> m RefAnnTerm
propagateRefinements (TName ty name) = do
  v' <- freshRefVar
  -- We could've avoided generating a fresh var and having to insert the extra conjunct,
  -- but it's perhaps safer to do so since it simplifies a later check that all refinement variables are unique.
  let refinement = addConjunct (AR $ tv v' |=| tv name) $ specRefinement v' $ tyRefinement ty
  pure $ TName (mkRefAnn refinement ty) name
propagateRefinements (TInteger ty n) = do
  v' <- freshRefVar
  let refinement = Refinement v' [AR $ tv v' |=| ti n]
  pure $ TInteger (mkRefAnn refinement ty) n
propagateRefinements (TBinOp ty t1 op t2) = do
  t1' <- propagateRefinements t1
  t2' <- propagateRefinements t2
  v' <- freshRefVar
  let refinement = Refinement v' [AR $ tv v' |=| TBinOp () (termSubjVarTerm t1') op (termSubjVarTerm t2')]
  pure $ TBinOp (mkRefAnn refinement ty) t1' op t2'
propagateRefinements (TApp ty fun arg) = do
  fun' <- propagateRefinements fun
  arg' <- propagateRefinements arg
  v' <- freshRefVar
  -- TODO add the symbolic `v' = fun arg` AR?
  let refinement = specRefinement v' $ tyRefinement ty
  pure $ TApp (mkRefAnn refinement ty) fun' arg'
propagateRefinements TIfThenElse { .. } = do
  tcond' <- propagateRefinements tcond
  tthen' <- propagateRefinements tthen
  telse' <- propagateRefinements telse
  v' <- freshRefVar
  let refinement = Refinement v' [AR $ TIfThenElse () (termSubjVarTerm tcond')
                                                      (tv v' |=| termSubjVarTerm tthen')
                                                      (tv v' |=| termSubjVarTerm telse')]
  pure $ TIfThenElse (mkRefAnn refinement annotation) tcond' tthen' telse'

mkRefAnn :: Refinement -> Ty -> RefAnn
mkRefAnn ref ty = RefAnn ref $ setTyRefinement ty ref

emptyQuery :: RefAnn -> QAnn
emptyQuery = VCAnn Nothing

genQueries :: MonadQ m => RefAnnTerm -> m QTerm
genQueries (TName ann name) = pure $ TName (emptyQuery ann) name
genQueries (TInteger ann n) = pure $ TInteger (emptyQuery ann) n
genQueries (TBinOp ann t1 op t2) = TBinOp (emptyQuery ann) <$> genQueries t1 <*> pure op <*> genQueries t2
genQueries  TIfThenElse { .. } = TIfThenElse (emptyQuery annotation) <$> genQueries tcond
                                                                     <*> genQueries tthen
                                                                     <*> genQueries telse
genQueries (TApp refAnn fun arg) = do
  fun' <- genQueries fun
  arg' <- genQueries arg
  query <- case (tyAnn $ annotation fun, tyAnn $ annotation arg) of
                (TyArrow ArrowTy { domTy = expectedTy }, actualTy) -> expectedTy <: actualTy
                (_, _) -> error "Function should have arrow type (this should've been caught earlier though)"
  pure $ TApp (emptyQuery refAnn) (setQuery query fun') arg'

(<:) :: MonadQ m => Ty -> Ty -> m Query
TyBase rbtActual <: TyBase rbtExpected = do
  v' <- freshRefVar
  let actual = specRefinement v' $ baseTyRefinement rbtActual
  let expected = specRefinement v' $ baseTyRefinement rbtExpected
  -- TODO this doesn't take the derived refinement into account — check when it breaks
  pure $ actual :=> expected
TyArrow (ArrowTy _ funDomTy funCodTy) <: TyArrow (ArrowTy _ argDomTy argCodTy) = do
  argQuery <- argDomTy <: funDomTy
  codQuery <- funCodTy <: argCodTy
  pure $ argQuery :& codQuery
ty1 <: ty2 = error [i|Mismatched types #{ty1} #{ty2} (which should've been caught earlier though)|]

-- Helpers
freshRefVar :: MonadQ m => m VarName
freshRefVar = do
  idx <- gets freeRefinementVarsCount
  modify' $ \st -> st { freeRefinementVarsCount = idx + 1 }
  pure [i|v#{idx}|]

specRefinement :: VarName -> Maybe Refinement -> Refinement
specRefinement var maybeRef = Refinement var ars
  where
    ars | Just ref <- maybeRef = renameVar' (Proxy :: Proxy ()) (subjectVar ref) var (conjuncts ref)
        | otherwise = []
