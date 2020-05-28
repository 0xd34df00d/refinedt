{-# LANGUAGE QuasiQuotes #-}

module T30TermsCompilerSpec(spec) where

import Data.String.Interpolate
import Test.Hspec

import Idris.IdeModeClient
import Toy.Language.BasicTC
import Toy.Language.Compiler
import Toy.Language.Solver

import TestUtils

checkIdris :: String -> IdrisHandle -> Expectation
checkIdris program ih = do
  (ctx, (funSig, funDef)) <- testParseFunWithCtx program
  let typedFunDef = annotateFunDef ctx funSig funDef
  res <- solve (buildCtx ctx) funSig typedFunDef
  res `shouldBe` Correct
  runIdrisClient ih $ withFile $ \file -> do
    mapM_ (write file . compileFunSig) ctx
    write file $ compileFunSig funSig
    write file $ compileFunDef funSig typedFunDef
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
    it "translates relational operations" $ checkIdris
      [i|
         gt : Int -> Int -> Bool
         gt a b = a > b
        |]
    it "translates applying function to a constant" $ checkIdris
      [i|
         f : (Int -> Int) -> Int
         f g = g 0
        |]
    it "translates applying function to a function" $ checkIdris
      [i|
         f : ((Int -> Int) -> Int) -> (Int -> Int) -> Int
         f g h = g h
        |]
    it "translates applying more functions to functions" $ checkIdris
      [i|
         f : ((Int -> Int) -> Int -> Int) -> (Int -> Int) -> Int
         f g h = (g h) (g h 0)
        |]
    it "translates if-then-else" $ checkIdris
      [i|
         max : Int -> Int -> Int
         max a b = if a > b then a else b
        |]
    describe "if-then-else fun" $ do
      it "translates if-then-else applied to a variable" $ checkIdris
        [i|
           sel : Bool -> (Int -> Int) -> (Int -> Int) -> Int -> Int
           sel b f g x = (if b then f else g) x
          |]
      it "translates a function applied to if-then-else" $ checkIdris
        [i|
           sel : Bool -> (Int -> Int) -> Int -> Int -> Int
           sel b f x y = f (if b then x else y)
          |]
      it "translates funapps inside if-then-else branches" $ checkIdris
        [i|
           sel : Bool -> (Int -> Int) -> (Int -> Int) -> Int -> Int -> Int
           sel b f g x y = if b then f x else g y
          |]
  describe "Basic context" $
    it "uses definitions" $ checkIdris
      [i|
         f : Int -> Int

         g : Int
         g = f 0
        |]
  describe "Terms with refined types" $ do
    it "translates constants" $ checkIdris
      [i|
         someNum : { v : Int | v = 42 }
         someNum = 42
        |]
