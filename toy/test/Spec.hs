{-# LANGUAGE OverloadedStrings #-}

import Control.Monad.State.Strict
import Data.Default
import Data.Void
import Test.Hspec
import Text.Megaparsec hiding (State)

import Toy.Language.Parser
import Toy.Language.Types

parse' :: ParsecT Void String (State ParseState) a -> String -> Either (ParseErrorBundle String Void) a
parse' p str = evalState (runParserT (p <* eof) "" str) def

infixr 0 ~~>
(~~>) :: (Show a, Show b, Eq a, Eq b) => Either a b -> b -> Expectation
parseRes ~~> expected = parseRes `shouldBe` Right expected

main :: IO ()
main = hspec $ do
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
  describe "Parsing with conjunctions" $ let p = parse' parseBaseRT in do
    it "parses types with conjunctions 1" $
      p "{ ν : Bool | ν < x & ν > 0 }" ~~> RefinedBaseTy TBool $ Refinement [AR ROpLe (RArgVar "x"), AR ROpGe RArgZero]
    it "parses types with conjunctions 2" $
      p "{ ν : Bool | ν < x & ν < len arr }" ~~> RefinedBaseTy TBool $ Refinement [AR ROpLe (RArgVar "x"), AR ROpLe (RArgVarLen "arr")]

-- Some helpers to make tests a tad more pleasant
infixr 0 -->
(-->) :: Ty -> Ty -> Ty
a --> b = TyArrow $ ArrowTy Nothing a b

bool, int :: Ty
bool = TyBase $ RefinedBaseTy TBool trueRefinement
int = TyBase $ RefinedBaseTy TInt trueRefinement
