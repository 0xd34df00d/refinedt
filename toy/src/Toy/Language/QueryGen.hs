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

data Query
  = Refinement :=> Refinement
  | Query :& Query
  deriving (Eq, Ord, Show)

-- The VC proposition `query` is whatever needs to hold for that specific term to type check (not including its subterms).
-- It assumes that `refAnn` holds.
data QAnn = QAnn
  { query :: Maybe Query
  , refAnn :: RefAnn
  } deriving (Eq, Ord, Show)

type QTerm = TermT QAnn

emptyQuery :: RefAnn -> QAnn
emptyQuery = QAnn Nothing

genQueries :: MonadQ m => RefAnnTerm -> m QTerm
genQueries (TName ann name) = pure $ TName (emptyQuery ann) name
genQueries (TInteger ann n) = pure $ TInteger (emptyQuery ann) n
genQueries (TBinOp ann t1 op t2) = TBinOp (emptyQuery ann) <$> genQueries t1 <*> pure op <*> genQueries t2
genQueries  TIfThenElse { .. } = TIfThenElse (emptyQuery tifeAnn) <$> genQueries tcond
                                                                  <*> genQueries tthen
                                                                  <*> genQueries telse
genQueries (TApp refAnn fun arg) = do
  fun' <- genQueries fun
  arg' <- genQueries arg
  query <- case (tyAnn $ annotation fun, tyAnn $ annotation arg) of
                (TyArrow ArrowTy { domTy = expectedTy }, actualTy) -> Just <$> expectedTy <: actualTy
                (_, _) -> error "Function should have arrow type (this should've been caught earlier though)"
  pure $ TApp QAnn { .. } fun' arg'

(<:) :: MonadQ m => Ty -> Ty -> m Query
TyBase rbtExpected <: TyBase rbtActual = do
  v' <- freshRefVar
  let actual = specRefinement v' $ baseTyRefinement rbtActual
  let expected = specRefinement v' $ baseTyRefinement rbtExpected
  pure $ actual :=> expected
TyArrow (ArrowTy _ funDomTy funCodTy) <: TyArrow (ArrowTy _ argDomTy argCodTy) = do
  argQuery <- argDomTy <: funDomTy
  codQuery <- funCodTy <: argCodTy
  pure $ argQuery :& codQuery
ty1 <: ty2 = error [i|Mismatched types #{ty1} #{ty2} (which should've been caught earlier though)|]

termSubjVar :: RefAnnTerm -> VarName
termSubjVar = subjectVar . intrinsic . annotation

termSubjVarTerm :: RefAnnTerm -> Term
termSubjVarTerm = TName () . termSubjVar

specRefinement :: VarName -> Maybe Refinement -> Refinement
specRefinement var maybeRef = Refinement var ars
  where
    ars | Just ref <- maybeRef = renameVar' (Proxy :: Proxy ()) (subjectVar ref) var (conjuncts ref)
        | otherwise = []
