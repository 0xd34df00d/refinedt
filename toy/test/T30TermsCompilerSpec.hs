{-# LANGUAGE QuasiQuotes #-}

module T30TermsCompilerSpec(spec) where

import Data.String.Interpolate
import Test.Hspec

import Idris.IdeModeClient
import Toy.Language.Compiler
import Toy.Language.Solver

import TestUtils

checkIdris :: String -> IdrisHandle -> Expectation
checkIdris program ih = do
  (ctx, (funSig, funDef)) <- testParseFunWithCtx program
  res <- solve (buildCtx ctx) funSig funDef
  res `shouldBe` Correct
  runIdrisClient ih $ withFile $ \file -> do
    mapM_ (write file . compileFunSig) ctx
    write file $ compileFunSig funSig
    write file $ compileFunDef funDef
    testIdrisFile file

spec :: Spec
spec = testWithIdris $ do
  describe "Terms with unrefined types" $ do
    it "translates constants" $ checkIdris
      [i|
         someNum : Int
         someNum = 42
        |]
    it "translates variables" $ checkIdris
      [i|
         id' : Int -> Int
         id' x = x
        |]
    it "translates binary arithmetic operations" $ checkIdris
      [i|
         add : Int -> Int -> Int
         add a b = a + b
        |]
