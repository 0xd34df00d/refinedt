{-# LANGUAGE FlexibleContexts, GADTs #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module TypesCompilerSpec(spec) where

import Control.Monad.IO.Class
import Control.Monad.Loops
import Control.Monad.State.Strict
import Data.Either
import Data.List.Extra
import QuickCheck.GenT
import Test.Hspec
import Test.QuickCheck(property)
import Text.SExpression

import Idris.IdeModeClient
import Toy.Language.Compiler
import Toy.Language.Parser.Decl
import Toy.Language.Syntax.Decl
import Toy.Language.Syntax.Types

import TestUtils

parseFunDecl :: String -> IO FunDecl
parseFunDecl str = do
  parsed `shouldSatisfy` isRight
  pure $ either (error . show) id parsed
  where
    parsed = parse' funDecl str

isReturn :: SExpr -> Bool
isReturn (List (Atom ":return" : _)) = True
isReturn _ = False

isOkReply :: SExpr -> Bool
isOkReply (List [Atom ":return", List (Atom ":ok" : _), _]) = True
isOkReply _ = False

checkIdris :: String -> IdrisHandle -> Expectation
checkIdris declStr ih = parseFunDecl declStr >>= checkIdrisFunDecl ih

checkIdrisFunDecl :: IdrisHandle -> FunDecl -> Expectation
checkIdrisFunDecl ih ty = runIdrisClient ih $ withFile $ \file -> do
  write file $ compileFunDecl ty
  sendCommand $ loadFile file
  reply <- iterateUntil isReturn readReply
  liftIO $ reply `shouldSatisfy` isOkReply

spec :: Spec
spec = parallel $ beforeAll startIdris $ afterAll stopIdris $ do
  describe "Basic smoke tests" $ do
    it "Compiles base types" $ checkIdris "someBool : Bool"
    describe "Compiles arrow types" $ do
      it "base types" $ checkIdris "someFun : Int -> Bool"
      it "refinements" $ checkIdris "someFun : { ν : Int | ν > 0 } -> Bool"
      it "pi-bound vars" $ checkIdris "someFun : (x : Int) -> Bool"
      it "pi-bound vars and refinements" $ checkIdris "someFun : (x : { ν : Int | ν > 0 }) -> Bool"
      it "pi-bound vars some more" $ checkIdris "someFun : (ls : IntList) -> { ν : Int | ν >= 0 & ν < len ls } -> Int"
  describe "QuickCheck fun" $
    it "Compiles arbitrarily generated types" $ \ih -> property $ checkIdrisFunDecl ih . FunDecl "testFun"

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
    genRefinement = Refinement . nub <$> listOf genAtomicRefinement
    genAtomicRefinement = AR <$> genRefinementOp <*> genRefinementArg
    genRefinementOp = elements enumerate
    genRefinementArg = do
      vars <- get
      elements $ RArgZero
               : [ RArgVar var | (var, TInt) <- vars ]
              <> [ RArgVarLen var | (var, TIntList) <- vars ]

instance MonadState s m => MonadState s (GenT m) where
  state = lift . state
  get = lift get
  put = lift . put
