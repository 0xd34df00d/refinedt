{-# LANGUAGE QuasiQuotes #-}

module T20TCSpec(spec) where

import Data.Char
import Data.Either
import Data.String.Interpolate
import Test.Hspec

import Toy.Language.Parser
import Toy.Language.Solver

import TestUtils

expectSolverOn :: SolveContext -> SolveRes -> String -> Expectation
expectSolverOn ctx expected str = do
  parseRes `shouldSatisfy` isRight

  let Right (sig, def) = parseRes
  res <- solve ctx sig def
  res `shouldBe` expected
  where
    parseRes = parse' fun $ trimHeading str

spec :: Spec
spec =
  describe "Basic smoke tests" $ do
    it "rejects `a + b ≥ a, a + b ≥ b` on (int, int)" $ expectSolverOn mempty Wrong
        [i|
           add : (x : Int) -> (y : Int) -> { ν : Int | ν >= x & ν >= y }
           add x y = x + y
          |]
    it "rejects `a + b ≥ a, a + b ≥ b` on (int, nat)" $ expectSolverOn mempty Wrong
        [i|
           add : (x : Int) -> (y : { ν : Int | ν >= 0 }) -> { ν : Int | ν >= x & ν >= y }
           add x y = x + y
          |]
    it "accepts `a + b ≥ a, a + b ≥ b` on (nat, nat)" $ expectSolverOn mempty Correct
        [i|
           add : (x : { ν : Int | ν >= 0 }) -> (y : { ν : Int | ν >= 0 }) -> { ν : Int | ν >= x & ν >= y }
           add x y = x + y
          |]
    it "accepts `a + b + a ≥ a, a + b + a ≥ b` on (nat, nat)" $ expectSolverOn mempty Correct
        [i|
           add : (x : { ν : Int | ν >= 0 }) -> (y : { ν : Int | ν >= 0 }) -> { ν : Int | ν >= x & ν >= y }
           add x y = x + y + x
          |]


trimHeading :: String -> String
trimHeading str = case flt $ lines str of
                       (l:ls) -> unlines $ flt $ drop (countLeading l) <$> l:ls
                       _ -> str
  where
    countLeading = length . takeWhile isSpace
    flt = filter $ not . null
