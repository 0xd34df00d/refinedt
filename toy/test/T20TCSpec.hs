{-# LANGUAGE QuasiQuotes #-}

module T20TCSpec(spec) where

import Data.Either
import Data.String.Interpolate
import Test.Hspec

import Toy.Language.Parser
import Toy.Language.Solver

import TestUtils

expectSolverOn :: SolveRes -> String -> Expectation
expectSolverOn expected str = do
  parseRes `shouldSatisfy` isRight

  let Right (ctx, (sig, def)) = parseRes
  res <- solve (buildCtx ctx) sig def
  res `shouldBe` expected
  where
    parseRes = parse' funWithCtx $ trimIndentation str

spec :: Spec
spec = do
  describe "Basic arithmetic" $ do
    it "rejects `a + b ≥ a, a + b ≥ b` on (int, int)" $ expectSolverOn Wrong
        [i|
           add : (x : Int) -> (y : Int) -> { ν : Int | ν >= x & ν >= y }
           add x y = x + y
          |]
    it "rejects `a + b ≥ a, a + b ≥ b` on (int, nat)" $ expectSolverOn Wrong
        [i|
           add : (x : Int) -> (y : { ν : Int | ν >= 0 }) -> { ν : Int | ν >= x & ν >= y }
           add x y = x + y
          |]
    it "accepts `a + b ≥ a, a + b ≥ b` on (nat, nat)" $ expectSolverOn Correct
        [i|
           add : (x : { ν : Int | ν >= 0 }) -> (y : { ν : Int | ν >= 0 }) -> { ν : Int | ν >= x & ν >= y }
           add x y = x + y
          |]
    it "accepts `a + b + a ≥ a, a + b + a ≥ b` on (nat, nat)" $ expectSolverOn Correct
        [i|
           add : (x : { ν : Int | ν >= 0 }) -> (y : { ν : Int | ν >= 0 }) -> { ν : Int | ν >= x & ν >= y }
           add x y = x + y + x
          |]
  describe "Path sensitivity" $ do
    it "accepts ReLu" $ expectSolverOn Correct
        [i|
           relu : Int -> { ν : Int | ν >= 0 }
           relu x = if x > 0 then x else 0
          |]
    it "accepts stricter ReLu" $ expectSolverOn Correct
        [i|
           relu : (x : Int) -> { ν : Int | ν >= 0 & ν >= x }
           relu x = if x > 0 then x else 0
          |]
    it "accepts max" $ expectSolverOn Correct
        [i|
           max : (x : Int) -> (y : Int) -> { ν : Int | ν >= x & ν >= y }
           max x y = if x > y then x else y
          |]
    it "rejects min as max" $ expectSolverOn Wrong
        [i|
           max : (x : Int) -> (y : Int) -> { ν : Int | ν >= x & ν >= y }
           max x y = if x > y then y else x
          |]
    it "accepts 3-max" $ expectSolverOn Correct
        [i|
           max : (x : Int) -> (y : Int) -> (z : Int) -> { ν : Int | ν >= x & ν >= y & ν >= z }
           max x y z = if x > y then if x > z then x else z else if y > z then y else z
          |]
  describe "Basic function application" $ do
    it "accepts correct subtyping queries" $ expectSolverOn Correct
        [i|
           g : { ν : Int | ν >= 0 } -> Int

           f : { ν : Int | ν > 0 } -> Int
           f x = g x
          |]
    it "rejects incorrect subtyping queries" $ expectSolverOn Wrong
        [i|
           g : { ν : Int | ν > 0 } -> Int

           f : { ν : Int | ν >= 0 } -> Int
           f x = g x
          |]
    it "accepts correct dependent subtyping queries" $ expectSolverOn Correct
        [i|
           g : (x : Int) -> (x1 : { ν : Int | ν >= x }) -> (x2 : { ν : Int | ν >= x1 }) -> Int

           f : (x : Int) -> (x1 : { ν : Int | ν > x }) -> (x2 : { ν : Int | ν > x1 }) -> Int
           f x x1 x2 = g x x1 x2
          |]
    it "accepts correct dependent subtyping queries (substituting)" $ expectSolverOn Correct
        [i|
           g : (z : Int) -> (z1 : { ν : Int | ν >= z }) -> (z2 : { ν : Int | ν >= z1 }) -> Int

           f : (x : Int) -> (x1 : { ν : Int | ν > x }) -> (x2 : { ν : Int | ν > x1 }) -> Int
           f x x1 x2 = g x x1 x2
          |]
    it "accepts correct dependent subtyping queries (substituting-2)" $ expectSolverOn Correct
        [i|
           g : (z : Int) -> (z1 : { ν : Int | ν >= z }) -> (z2 : { ν : Int | ν >= z1 }) -> Int

           f : (x1 : { ν : Int | ν > 0 }) -> (x2 : { ν : Int | ν > x1 }) -> Int
           f x1 x2 = g 0 x1 x2
          |]
    it "rejects incorrect dependent subtyping queries" $ expectSolverOn Wrong
        [i|
           g : (x : Int) -> (x1 : { ν : Int | ν > x }) -> (x2 : { ν : Int | ν > x1 }) -> Int

           f : (x : Int) -> (x1 : { ν : Int | ν >= x }) -> (x2 : { ν : Int | ν >= x1 }) -> Int
           f x x1 x2 = g x x1 x2
          |]
    it "rejects incorrect dependent subtyping queries (substituting)" $ expectSolverOn Wrong
        [i|
           g : (x : Int) -> (x1 : { ν : Int | ν > x }) -> (x2 : { ν : Int | ν > x1 }) -> Int

           f : (x : { ν : Int | ν >= 0 }) -> (y : { ν : Int | ν >= x }) -> Int
           f x y = g 0 x y
          |]
    it "accepts max(x, 0)" $ expectSolverOn Correct
        [i|
           max : (x : Int) -> (y : Int) -> { ν : Int | ν >= x & ν >= y }

           f : Int -> { ν : Int | ν >= 0 }
           f x = max x 0
          |]
    it "accepts max(x, 0) with max as arg" $ expectSolverOn Correct
        [i|
           f : (max : (x : Int) -> (y : Int) -> { ν : Int | ν >= x & ν >= y }) -> Int -> { ν : Int | ν >= 0 }
           f max x = max x 0
          |]
    it "accepts add(x, 0)" $ expectSolverOn Correct
        [i|
           add : (x : { ν : Int | ν >= 0 }) -> (y : { ν : Int | ν >= 0 }) -> { ν : Int | ν >= x & ν >= y }

           f : (x : { ν : Int | ν >= 0 }) -> { ν : Int | ν >= 0 & ν >= x }
           f x = add x 0
          |]
    it "accepts passing functions to functions" $ expectSolverOn Correct
        [i|
           f : (x : { ν : Int | ν >= 0 }) -> (y : { ν : Int | ν >= 0 }) -> { ν : Int | ν >= 0 }

           g : ((x : { ν : Int | ν >= 0 }) -> (y : { ν : Int | ν >= 0 }) -> { ν : Int | ν >= 0 }) -> Int

           h : Int
           h = g f
          |]
    it "accepts correct functional argument refinements" $ expectSolverOn Correct
        [i|
           f : (x : { ν : Int | ν >= 0 }) -> (y : { ν : Int | ν >= 0 }) -> { ν : Int | ν > 0 }

           g : ((x : { ν : Int | ν > 0 }) -> (y : { ν : Int | ν > 0 }) -> { ν : Int | ν >= 0 }) -> Int

           h : Int
           h = g f
          |]
    it "rejects incorrect functional argument refinements (on dom)" $ expectSolverOn Wrong
        [i|
           f : (x : { ν : Int | ν > 0 }) -> (y : { ν : Int | ν >= 0 }) -> { ν : Int | ν > 0 }

           g : ((x : { ν : Int | ν >= 0 }) -> (y : { ν : Int | ν > 0 }) -> { ν : Int | ν >= 0 }) -> Int

           h : Int
           h = g f
          |]
    it "rejects incorrect functional argument refinements (on cod)" $ expectSolverOn Wrong
        [i|
           f : (x : { ν : Int | ν >= 0 }) -> (y : { ν : Int | ν >= 0 }) -> { ν : Int | ν >= 0 }

           g : ((x : { ν : Int | ν >= 0 }) -> (y : { ν : Int | ν > 0 }) -> { ν : Int | ν > 0 }) -> Int

           h : Int
           h = g f
          |]
