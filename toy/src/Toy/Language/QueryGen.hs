{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}

module Toy.Language.QueryGen where

import Control.Monad.State.Strict
import Data.String.Interpolate.IsString

import Toy.Language.Syntax.Common
import Toy.Language.Syntax.Decls
import Toy.Language.Syntax.Terms
import Toy.Language.Syntax.Terms.Sugar
import Toy.Language.Syntax.Types

-- The intrinsic refinement characterizes the structure of the term and doesn't need to be checked but can be assumed.
-- The VC proposition is whatever needs to hold for that specific term to type check (not including its subterms).
data QAnnotation = QAnnotation
  { intrinsic :: Maybe Refinement
  , tyAnn :: Ty
  } deriving (Eq, Ord, Show)

type QTerm = TermT QAnnotation
type QFunDef = FunDefT QAnnotation

emptyQAnn :: Maybe Refinement -> TypedTerm -> QTerm
emptyQAnn = fmap . QAnnotation

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
genQueries t@(TName ty _) = pure $ emptyQAnn (tyRefinement ty) t
genQueries (TInteger ty n) = do
  v' <- freshRefVar
  let refinement = Just $ Refinement v' [AR $ tv v' |=| ti n]
  pure $ TInteger (QAnnotation refinement ty) n
