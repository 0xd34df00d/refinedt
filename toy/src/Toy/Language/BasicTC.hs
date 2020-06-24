{-# LANGUAGE RecordWildCards, QuasiQuotes #-}
{-# LANGUAGE FlexibleContexts #-}

module Toy.Language.BasicTC where

import qualified Data.HashMap.Strict as HM
import Data.Generics.Uniplate.Data
import Data.String.Interpolate
import Control.Monad.Reader

import Toy.Language.EnvironmentUtils
import Toy.Language.Syntax

annotateTypes :: MonadReader Var2Ty m => Term -> m TypedTerm
annotateTypes (TName _ varName) = asks $ (`TName` varName) . (HM.! varName)
annotateTypes (TInteger _ n) = pure $ TInteger (TyBase $ RefinedBaseTy TInt trueRefinement) n
annotateTypes (TBinOp _ t1 op t2) = do
  t1' <- annotateTypes t1
  t2' <- annotateTypes t2
  expectBaseTy TInt $ annotation t1'
  expectBaseTy TInt $ annotation t2'
  let resTy | op `elem` [BinOpPlus, BinOpMinus] = TInt
            | otherwise = TBool
  pure $ TBinOp (TyBase $ RefinedBaseTy resTy trueRefinement) t1' op t2'
annotateTypes TIfThenElse { annotation = _, .. } = do
  tcond' <- annotateTypes tcond
  expectBaseTy TBool $ annotation tcond'

  tthen' <- fmap stripRefinements <$> annotateTypes tthen
  telse' <- fmap stripRefinements <$> annotateTypes telse

  when (annotation tthen' /= annotation telse') $ error [i|Type mismatch between #{tthen} and #{telse}|]

  pure $ TIfThenElse (annotation tthen') tcond' tthen' telse'
annotateTypes (TApp _ t1 t2) = do
  t1' <- annotateTypes t1
  t2' <- annotateTypes t2
  resTy <- case annotation t1' of
                TyArrow ArrowTy { .. } -> do
                  when (stripRefinements domTy /= stripRefinements (annotation t2'))
                      $ error [i|Type mismatch: expected #{domTy}, got #{annotation t2'}|]
                  pure $ case piVarName of
                              Nothing -> codTy
                              Just varName -> substPi varName t2 codTy
                _ -> error [i|Expected arrow type, got #{annotation t1'}|]
  pure $ TApp resTy t1' t2'

annotateFunDef :: [FunSig] -> FunSig -> FunDef -> TypedFunDef
annotateFunDef ctx sig def@FunDef { .. } = FunDef { funBody = funBody', .. }
  where
    typesMapping = buildTypesMapping ctx $ fst $ funTypesMapping sig def
    funBody' = runReader (annotateTypes funBody) typesMapping

-- TODO rename whatever can be shadowed
substPi :: VarName -> Term -> Ty -> Ty
substPi srcName with = transformBi f
  where
    f (TName _ name) | name == srcName = with
    f arg = arg

expectBaseTy :: Monad m => BaseTy -> Ty -> m ()
expectBaseTy expected (TyBase RefinedBaseTy { .. }) | baseType == expected = pure ()
expectBaseTy expected ty = error [i|Expected #{expected}, got #{ty} instead|]
