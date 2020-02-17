{-# LANGUAGE OverloadedStrings #-}

import Data.Void
import Test.Hspec
import Text.Megaparsec

import Toy.Language.Parser
import Toy.Language.Types

parse' :: Parsec Void String a -> String -> Either (ParseErrorBundle String Void) a
parse' p = parse (p <* eof) ""

main :: IO ()
main = hspec $
  describe "Parsing base refined types" $ do
    it "parses unrefined type" $
      parse' parseBaseRT "Bool" `shouldBe` Right (RefinedBaseTy TBool trueRefinement)
    it "parses refined type with var" $
      parse' parseBaseRT "{ ν : Bool | ν < x }" `shouldBe` Right (RefinedBaseTy TBool $ Refinement [AR ROpLe (RArgVar "x")])
    it "parses refined type with zero" $
      parse' parseBaseRT "{ ν : Bool | ν <= 0 }" `shouldBe` Right (RefinedBaseTy TBool $ Refinement [AR ROpLeq RArgZero])
    it "parses refined type with len" $
      parse' parseBaseRT "{ ν : Bool | ν >= len arr }" `shouldBe` Right (RefinedBaseTy TBool $ Refinement [AR ROpGeq (RArgVarLen "arr")])
    it "parses refined type without spaces" $
      parse' parseBaseRT "{ν:Bool|ν>=len arr}" `shouldBe` Right (RefinedBaseTy TBool $ Refinement [AR ROpGeq (RArgVarLen "arr")])
