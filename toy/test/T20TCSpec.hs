{-# LANGUAGE QuasiQuotes #-}

module T20TCSpec(spec) where

import Data.String.Interpolate
import Test.Hspec

import Toy.Language.BasicTC
import Toy.Language.Solver

import TestUtils

expectSolverOn :: SolveRes -> String -> Expectation
expectSolverOn expected str = do
  (ctx, (sig, def)) <- testParseFunWithCtx str
  let typedDef = annotateFunDef ctx sig def
  let qdef = genQueriesFunDef sig typedDef
  (res, _) <- solveDef sig qdef
  res `shouldBe` expected

spec :: Spec
spec = do
  describe "Basic logic" $ do
    it "propagates the same refinement" $ expectSolverOn Correct
        [i|
           id' : (x : { v : Int | v >= 0 }) -> { v : Int | v >= 0 }
           id' x = x
          |]
    it "accepts correct implication" $ expectSolverOn Correct
        [i|
           id' : (x : { v : Int | v > 0 }) -> { v : Int | v >= 0 }
           id' x = x
          |]
    it "rejects incorrect implication" $ expectSolverOn Wrong
        [i|
           id' : (x : { v : Int | v >= 0 }) -> { v : Int | v > 0 }
           id' x = x
          |]
  describe "Basic arithmetic" $ do
    it "rejects `a + b ≥ 0, a + b ≥ 0` on (int, int)" $ expectSolverOn Wrong
        [i|
           add : (x : Int) -> (y : Int) -> { v : Int | v >= 0 & v >= 0 }
           add x y = x + y
          |]
    it "accepts `a + b ≥ 0, a + b ≥ 0` on (nat, nat)" $ expectSolverOn Correct
        [i|
           add : (x : { v : Int | v >= 0 }) -> (y : { v : Int | v >= 0 }) -> { v : Int | v >= 0 & v >= 0 }
           add x y = x + y
          |]
    it "rejects `a + b ≥ a, a + b ≥ b` on (int, int)" $ expectSolverOn Wrong
        [i|
           add : (x : Int) -> (y : Int) -> { v : Int | v >= x & v >= y }
           add x y = x + y
          |]
    it "rejects `a + b ≥ a, a + b ≥ b` on (int, nat)" $ expectSolverOn Wrong
        [i|
           add : (x : Int) -> (y : { v : Int | v >= 0 }) -> { v : Int | v >= x & v >= y }
           add x y = x + y
          |]
    it "accepts `a + b ≥ a, a + b ≥ b` on (nat, nat)" $ expectSolverOn Correct
        [i|
           add : (x : { v : Int | v >= 0 }) -> (y : { v : Int | v >= 0 }) -> { v : Int | v >= x & v >= y }
           add x y = x + y
          |]
    it "accepts `a + b + a ≥ a, a + b + a ≥ b` on (nat, nat)" $ expectSolverOn Correct
        [i|
           add : (x : { v : Int | v >= 0 }) -> (y : { v : Int | v >= 0 }) -> { v : Int | v >= x & v >= y }
           add x y = x + y + x
          |]
  describe "Path sensitivity" $ do
    it "accepts ReLu" $ expectSolverOn Correct
        [i|
           relu : Int -> { v : Int | v >= 0 }
           relu x = if x > 0 then x else 0
          |]
    it "accepts stricter ReLu" $ expectSolverOn Correct
        [i|
           relu : (x : Int) -> { v : Int | v >= 0 & v >= x }
           relu x = if x > 0 then x else 0
          |]
    it "accepts max" $ expectSolverOn Correct
        [i|
           max : (x : Int) -> (y : Int) -> { v : Int | v >= x & v >= y }
           max x y = if x > y then x else y
          |]
    it "rejects min as max" $ expectSolverOn Wrong
        [i|
           max : (x : Int) -> (y : Int) -> { v : Int | v >= x & v >= y }
           max x y = if x > y then y else x
          |]
    it "accepts 3-max" $ expectSolverOn Correct
        [i|
           max : (x : Int) -> (y : Int) -> (z : Int) -> { v : Int | v >= x & v >= y & v >= z }
           max x y z = if x > y then if x > z then x else z else if y > z then y else z
          |]
  describe "Basic function application" $ do
    it "accepts correct subtyping queries" $ expectSolverOn Correct
        [i|
           g : { v : Int | v >= 0 } -> Int

           f : { v : Int | v > 0 } -> Int
           f x = g x
          |]
    it "rejects incorrect subtyping queries" $ expectSolverOn Wrong
        [i|
           g : { v : Int | v > 0 } -> Int

           f : { v : Int | v >= 0 } -> Int
           f x = g x
          |]
    it "accepts correct dependent subtyping queries" $ expectSolverOn Correct
        [i|
           g : (x : Int) -> (x1 : { v : Int | v >= x }) -> (x2 : { v : Int | v >= x1 }) -> Int

           f : (x : Int) -> (x1 : { v : Int | v > x }) -> (x2 : { v : Int | v > x1 }) -> Int
           f x x1 x2 = g x x1 x2
          |]
    it "accepts correct dependent subtyping queries (substituting)" $ expectSolverOn Correct
        [i|
           g : (z : Int) -> (z1 : { v : Int | v >= z }) -> (z2 : { v : Int | v >= z1 }) -> Int

           f : (x : Int) -> (x1 : { v : Int | v > x }) -> (x2 : { v : Int | v > x1 }) -> Int
           f x x1 x2 = g x x1 x2
          |]
    it "accepts correct dependent subtyping queries (substituting-2)" $ expectSolverOn Correct
        [i|
           g : (z : Int) -> (z1 : { v : Int | v >= z }) -> (z2 : { v : Int | v >= z1 }) -> Int

           f : (x1 : { v : Int | v > 0 }) -> (x2 : { v : Int | v > x1 }) -> Int
           f x1 x2 = g 0 x1 x2
          |]
    it "rejects incorrect dependent subtyping queries" $ expectSolverOn Wrong
        [i|
           g : (x : Int) -> (x1 : { v : Int | v > x }) -> (x2 : { v : Int | v > x1 }) -> Int

           f : (x : Int) -> (x1 : { v : Int | v >= x }) -> (x2 : { v : Int | v >= x1 }) -> Int
           f x x1 x2 = g x x1 x2
          |]
    it "rejects incorrect dependent subtyping queries (substituting)" $ expectSolverOn Wrong
        [i|
           g : (x : Int) -> (x1 : { v : Int | v > x }) -> (x2 : { v : Int | v > x1 }) -> Int

           f : (x : { v : Int | v >= 0 }) -> (y : { v : Int | v >= x }) -> Int
           f x y = g 0 x y
          |]
    it "accepts max(x, 0)" $ expectSolverOn Correct
        [i|
           max : (x : Int) -> (y : Int) -> { v : Int | v >= x & v >= y }

           f : Int -> { v : Int | v >= 0 }
           f x = max x 0
          |]
    it "accepts max(x, 0) with max as arg" $ expectSolverOn Correct
        [i|
           f : (max : (x : Int) -> (y : Int) -> { v : Int | v >= x & v >= y }) -> Int -> { v : Int | v >= 0 }
           f max x = max x 0
          |]
    it "accepts add(x, 0)" $ expectSolverOn Correct
        [i|
           add : (x : { v : Int | v >= 0 }) -> (y : { v : Int | v >= 0 }) -> { v : Int | v >= x & v >= y }

           f : (x : { v : Int | v >= 0 }) -> { v : Int | v >= 0 & v >= x }
           f x = add x 0
          |]
    it "accepts passing functions to functions" $ expectSolverOn Correct
        [i|
           f : (x : { v : Int | v >= 0 }) -> (y : { v : Int | v >= 0 }) -> { v : Int | v >= 0 }

           g : ((x : { v : Int | v >= 0 }) -> (y : { v : Int | v >= 0 }) -> { v : Int | v >= 0 }) -> Int

           h : Int
           h = g f
          |]
    it "accepts correct functional argument refinements" $ expectSolverOn Correct
        [i|
           f : (x : { v : Int | v >= 0 }) -> (y : { v : Int | v >= 0 }) -> { v : Int | v > 0 }

           g : ((x : { v : Int | v > 0 }) -> (y : { v : Int | v > 0 }) -> { v : Int | v >= 0 }) -> Int

           h : Int
           h = g f
          |]
    it "rejects incorrect functional argument refinements (on dom)" $ expectSolverOn Wrong
        [i|
           f : (x : { v : Int | v > 0 }) -> (y : { v : Int | v >= 0 }) -> { v : Int | v > 0 }

           g : ((x : { v : Int | v >= 0 }) -> (y : { v : Int | v > 0 }) -> { v : Int | v >= 0 }) -> Int

           h : Int
           h = g f
          |]
    it "rejects incorrect functional argument refinements (on cod)" $ expectSolverOn Wrong
        [i|
           f : (x : { v : Int | v >= 0 }) -> (y : { v : Int | v >= 0 }) -> { v : Int | v >= 0 }

           g : ((x : { v : Int | v >= 0 }) -> (y : { v : Int | v > 0 }) -> { v : Int | v > 0 }) -> Int

           h : Int
           h = g f
          |]
    it "accepts correct results of function application" $ expectSolverOn Correct
        [i|
           f : (x : { v : Int | v >= 0 }) -> (y : { v : Int | v >= 0 }) -> { v : Int | v > 0 }

           g : ((x : { v : Int | v > 0 }) -> (y : { v : Int | v > 0 }) -> { v : Int | v >= 0 }) -> { v : Int | v >= 0 }

           h : { v : Int | v >= 0 }
           h = g f
          |]
    it "rejects incorrect results of function application" $ expectSolverOn Wrong
        [i|
           f : (x : { v : Int | v >= 0 }) -> (y : { v : Int | v >= 0 }) -> { v : Int | v > 0 }

           g : ((x : { v : Int | v > 0 }) -> (y : { v : Int | v > 0 }) -> { v : Int | v >= 0 }) -> { v : Int | v >= 0 }

           h : { v : Int | v > 0 }
           h = g f
          |]
    it "accepts more complicated function application" $ expectSolverOn Correct
        [i|
           f : { v : Int | v >= 0 } -> { v : Int | v > 0 }
           h : { v : Int | v >= 0 } -> { v : Int | v > 0 }
           g : { v : Int | v >= 0 } -> { v : Int | v >= 0 } -> { v : Int | v > 0 }

           fun : { v : Int | v > 0 } -> { v : Int | v > 0 } -> { v : Int | v >= 0 }
           fun x y = g (f x) (h y)
          |]
    it "accepts yet more complicated function application" $ expectSolverOn Correct
        [i|
           f : (x : { v : Int | v >= 0 }) -> { v : Int | v > x }
           g : (x : Int) -> { v : Int | v > 0 }

           fun : (x : { v : Int | v > 0 }) -> { v : Int | v >= 0 }
           fun x = g (f x)
          |]
    xit "accepts yet more complicated function application" $ expectSolverOn Correct
        [i|
           f : (x : { v : Int | v >= 0 }) -> { v : Int | v > x }
           g : (x : Int) -> { v : Int | v > x }

           fun : (x : { v : Int | v > 0 }) -> { v : Int | v >= x }
           fun x = g (f x)
          |]
    xit "accepts yet more complicated function application" $ expectSolverOn Correct
        [i|
           f : (x : { v : Int | v >= 0 }) -> { v : Int | v > x }
           h : (x : { v : Int | v >= 0 }) -> { v : Int | v > x }
           g : (x : Int) -> (y : Int) -> (x' : { v : Int | v >= x }) -> (y' : { v : Int | v >= y }) -> { v : Int | v > x & v > y }

           fun : (x : { v : Int | v > 0 }) -> (y : { v : Int | v > 0 }) -> { v : Int | v >= x & v >= y}
           fun x y = g x y (f x) (h y)
          |]
  describe "Z3 fun" $ do
    it "accepts a function on bools" $ expectSolverOn Correct
      [i|
         gt : Bool -> Bool
         gt b = b
        |]
    it "accepts a function taking ints and returning a bool" $ expectSolverOn Correct
      [i|
         gt : Int -> Int -> Bool
         gt a b = a > b
        |]
