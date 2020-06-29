{-# LANGUAGE RecordWildCards #-}

module Toy.Language.EnvironmentUtils
( funTypesMapping
, buildCombinedMapping
, buildTypesMapping
, retType
, splitTypes

, ArgTypes
, Var2Ty
) where

import qualified Data.HashMap.Strict as HM
import Control.Applicative
import Control.Arrow
import Control.Monad.Identity

import Toy.Language.Syntax

type ArgTypes = [(VarName, Ty)]

type Var2Ty = HM.HashMap VarName Ty

funTypesMapping :: FunSig -> FunDefT a -> (ArgTypes, RefinedBaseTy)
funTypesMapping sig def = (arg2type, resType)
  where
    (argTypes, resType) = splitTypes $ funTy sig
    arg2type = zip (funArgs def) argTypes

retType :: FunSig -> RefinedBaseTy
retType = snd . splitTypes . funTy

splitTypes :: Ty -> ([Ty], RefinedBaseTy)
splitTypes (TyBase rbTy) = ([], rbTy)
splitTypes (TyArrow ArrowTy { .. }) = first (domTy :) $ splitTypes codTy

buildVarsMap :: Monad m => (VarName -> Ty -> m a) -> ArgTypes -> m (HM.HashMap VarName a)
buildVarsMap f args = HM.fromList <$> mapM sequence [ (var, f var ty) | (var, ty) <- args ]

buildCombinedMapping :: Monad m => [FunSig] -> ArgTypes -> (VarName -> Ty -> m a) -> m (HM.HashMap VarName a)
buildCombinedMapping sigs args f = liftA2 (<>) (buildVarsMap f args) (buildVarsMap f sigs')
  where
    sigs' = [ (VarName funName, funTy) | FunSig { .. } <- sigs ]

buildTypesMapping :: [FunSig] -> ArgTypes -> Var2Ty
buildTypesMapping sigs args = runIdentity $ buildCombinedMapping sigs args $ \_ ty -> pure ty
