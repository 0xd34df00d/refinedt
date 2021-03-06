{-# LANGUAGE FlexibleContexts, GADTs #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
{-# LANGUAGE RecordWildCards, OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module T05TypesCompilerSpec(spec) where

import Control.Monad.State.Strict
import Data.Either
import Data.List.Extra
import QuickCheck.GenT
import Test.Hspec
import Test.QuickCheck(property)

import Idris.IdeModeClient
import Toy.Language.Compiler
import Toy.Language.Parser.Decl
import Toy.Language.Syntax
import Toy.Language.Syntax.Terms.Sugar

import TestUtils

parseFunDecl :: String -> IO FunSig
parseFunDecl str = do
  parsed `shouldSatisfy` isRight
  pure $ either (error . show) id parsed
  where
    parsed = parse' funSig str

checkIdris :: String -> IdrisHandle -> Expectation
checkIdris declStr ih = parseFunDecl declStr >>= checkIdrisFunDecl ih

checkIdrisFunDecl :: IdrisHandle -> FunSig -> Expectation
checkIdrisFunDecl ih ty = runIdrisClient ih $ withFile $ \file -> do
  writePrelude file
  write file $ compileFunSig ty
  testIdrisFile file

spec :: Spec
spec = testWithIdris $ do
  describe "Basic smoke tests" $ do
    it "Compiles base types" $ checkIdris "someBool : Bool"
    describe "Compiles arrow types" $ do
      it "base types" $ checkIdris "someFun : Int -> Bool"
      it "refinements" $ checkIdris "someFun : { v : Int | v > 0 } -> Bool"
      it "pi-bound vars" $ checkIdris "someFun : (x : Int) -> Bool"
      it "pi-bound vars and refinements" $ checkIdris "someFun : (x : { v : Int | v > 0 }) -> Bool"
      it "pi-bound vars referred in result" $ checkIdris "someFun : (x : Int) -> { v : Int | v >= 0 & v < x }"
      it "pi-bound vars referred in another refinement " $ checkIdris "someFun : (x : Int) -> { v : Int | v >= 0 & v < x } -> Int"
      it "pi-bound vars some more" $
        checkIdris "someFun : (len : IntList -> Int) -> (ls : IntList) -> { v : Int | v >= 0 & v < len ls } -> Int"
      it "pi-bound unrefined vars mentioned in subsequent refinements" $
        checkIdris "add : (x : Int) -> (y : Int) -> { v : Int | v >= x & v >= y }"
      it "pi-bound vars with refinements referring refinements" $
        checkIdris "add : (x : { v : Int | v >= 0 }) -> (y : { v : Int | v >= 0 }) -> { v : Int | v >= x & v >= y }"
  describe "QuickCheck fun" $
    xit "Compiles arbitrarily generated types" $ \ih -> property $ checkIdrisFunDecl ih . FunSig "testFun"

instance Arbitrary Ty where
  arbitrary = (`evalState` []) <$> runGenT (scale (`div` 10) $ sized $ genTy True)

genTy :: MonadState [(VarName, BaseTy)] m => Bool -> Int -> GenT m Ty
genTy isRoot n
  | isRoot = TyArrow <$> genTyArrow
  | n == 0 = TyBase <$> genTyBase
  | otherwise = frequency [ (3, TyArrow <$> genTyArrow)
                          , (2, TyBase <$> genTyBase)
                          ]
  where
    genTyArrow = do
      domTy <- genTy False $ n `div` 2
      piVarName <- case domTy of
                        TyArrow {} -> pure Nothing
                        TyBase rbTy -> do
                          cnt <- gets length
                          let name = VarName $ "a" <> show cnt
                          modify' ((name, baseType rbTy) :)
                          pure $ Just name
      codTy <- genTy False $ n `div` 2
      pure ArrowTy { .. }

    genTyBase = do
      baseType <- elements enumerate
      baseTyRefinement <- case baseType of
                               TInt -> genRefinement
                               _ -> pure trueRefinement
      pure $ RefinedBaseTy { .. }
    genRefinement = Just . Refinement v . nub <$> listOf genAtomicRefinement
    genAtomicRefinement = (\op arg -> AR $ TBinOp () v op arg) <$> genRefinementOp <*> genRefinementArg
    genRefinementOp = elements enumerate
    genRefinementArg = do
      vars <- get
      elements $ TInteger () 0
               : [ TName () var | (var, TInt) <- vars ]
              <> [ TApp () "len" $ TName () var | (var, TIntList) <- vars ]

instance MonadState s m => MonadState s (GenT m) where
  state = lift . state
  get = lift get
  put = lift . put
