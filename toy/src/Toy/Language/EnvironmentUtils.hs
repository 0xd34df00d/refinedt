{-# LANGUAGE RecordWildCards #-}

module Toy.Language.EnvironmentUtils where

import qualified Data.HashMap.Strict as HM
import Control.Applicative

import Toy.Language.Syntax.Decls
import Toy.Language.Syntax.Types

type ArgTypes = [(VarName, Ty)]

buildVarsMap :: Monad m => (VarName -> Ty -> m a) -> ArgTypes -> m (HM.HashMap VarName a)
buildVarsMap f args = HM.fromList <$> mapM sequence [ (var, f var ty) | (var, ty) <- args ]

buildCombinedMapping :: Monad m => [FunSig] -> ArgTypes -> (VarName -> Ty -> m a) -> m (HM.HashMap VarName a)
buildCombinedMapping sigs args f = liftA2 (<>) (buildVarsMap f args) (buildVarsMap f sigs')
  where
    sigs' = [ (VarName funName, funTy) | FunSig { .. } <- sigs ]
