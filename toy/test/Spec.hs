{-# LANGUAGE OverloadedStrings #-}

import Data.Void
import Test.Hspec
import Text.Megaparsec

import Toy.Language.Parser
import Toy.Language.Types

parse' :: Parsec Void String a -> String -> Either (ParseErrorBundle String Void) a
parse' p = parse (p <* eof) ""

infixr 0 ~~>
(~~>) :: (Show a, Show b, Eq a, Eq b) => Either a b -> b -> Expectation
parseRes ~~> expected = parseRes `shouldBe` Right expected

main :: IO ()
main = hspec $
  describe "Parsing base refined types" $ let p = parse' parseBaseRT in do
    it "parses unrefined type" $
      p "Bool" ~~> RefinedBaseTy TBool trueRefinement
    it "parses refined type with var" $
      p "{ ν : Bool | ν < x }" ~~> RefinedBaseTy TBool $ Refinement [AR ROpLe (RArgVar "x")]
    it "parses refined type with zero" $
      p "{ ν : Bool | ν <= 0 }" ~~> RefinedBaseTy TBool $ Refinement [AR ROpLeq RArgZero]
    it "parses refined type with len" $
      p "{ ν : Bool | ν >= len arr }" ~~> RefinedBaseTy TBool $ Refinement [AR ROpGeq (RArgVarLen "arr")]
    it "parses refined type without spaces" $
      p "{ν:Bool|ν>=len arr}" ~~> RefinedBaseTy TBool $ Refinement [AR ROpGeq (RArgVarLen "arr")]
    it "parses refined type with var name starting with len" $
      p "{ ν : Bool | ν >= lenarr }" ~~> RefinedBaseTy TBool $ Refinement [AR ROpGeq (RArgVar "lenarr")]
