{-# LANGUAGE OverloadedStrings #-}

module ParserSpec(spec) where

import Data.Bifunctor
import Data.Void
import Test.Hspec
import Text.Megaparsec hiding (State)

import Toy.Language.Parser.Ty
import Toy.Language.Syntax.Types

parse' :: Parsec Void String a -> String -> Either (ParseErrorBundle String Void) a
parse' p = runParser (p <* eof) ""

newtype ErrorMsg = ErrorMsg { getErrorMsg :: String } deriving (Eq)

instance Show ErrorMsg where
  show = getErrorMsg

infixr 0 ~~>
(~~>) :: (Show r, Eq r) => Either (ParseErrorBundle String Void) r -> r -> Expectation
parseRes ~~> expected = first (ErrorMsg . errorBundlePretty) parseRes `shouldBe` Right expected

spec :: Spec
spec = do
  describe "Parsing base refined types" $ let p = parse' baseRT in do
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
  describe "Parsing with conjunctions" $ let p = parse' baseRT in do
    it "parses types with conjunctions 1" $
      p "{ ν : Bool | ν < x & ν > 0 }" ~~> RefinedBaseTy TBool $ Refinement [AR ROpLe (RArgVar "x"), AR ROpGe RArgZero]
    it "parses types with conjunctions 2" $
      p "{ ν : Bool | ν < x & ν < len arr }" ~~> RefinedBaseTy TBool $ Refinement [AR ROpLe (RArgVar "x"), AR ROpLe (RArgVarLen "arr")]
  describe "Parsing arrows" $ let p = parse' ty in do
    it "still parses base types" $
      p "{ ν : Bool | ν >= len arr }" ~~> TyBase $ RefinedBaseTy TBool $ Refinement [AR ROpGeq (RArgVarLen "arr")]
    it "parses unrefined base types with parens" $
      p "(Bool)" ~~> bool
    it "parses simple arrows" $
      p "Bool -> Int" ~~> bool --> int
    it "parses simple arrows with parens" $
      p "(Bool -> Int)" ~~> bool --> int
    it "parses nested arrows (to the right)" $
      p "Bool -> Int -> Bool" ~~> bool --> int --> bool
    it "parses nested arrows (to the right, with parens)" $
      p "Bool -> (Int -> Bool)" ~~> bool --> int --> bool
    it "parses nested arrows (to the left)" $
      p "(Bool -> Int) -> Bool" ~~> (bool --> int) --> bool
    it "parses more nested arrows" $
      p "((Bool -> Int) -> Bool) -> (Bool -> Bool)" ~~> ((bool --> int) --> bool) --> (bool --> bool)
  describe "Parsing full refined types with arrows" $ let p = parse' ty in do
    it "parses simple arrows" $
      p "{ ν : Int | ν <= len arr } -> { ν : Int | ν > 0 }" ~~> intLeqLenArr --> intGe0
    it "parses simple arrows in parens" $
      p "({ ν : Int | ν <= len arr } -> { ν : Int | ν > 0 })" ~~> intLeqLenArr --> intGe0
    it "parses nested arrows" $
      p "{ ν : Int | ν <= len arr } -> { ν : Int | ν < var1 } -> { ν : Int | ν < var2 }"
        ~~> intLeqLenArr --> intLe "var1" --> intLe "var2"
    it "parses nested arrows with parens" $
      p "({ ν : Int | ν <= len arr } -> { ν : Int | ν < var1 }) -> { ν : Int | ν < var2 }"
        ~~> (intLeqLenArr --> intLe "var1") --> intLe "var2"
  describe "Parsing arrows and pi-bound variables" $ let p = parse' ty in do
    it "parses pi-bound unrefined types" $
      p "x : Bool -> Bool" ~~> "x".:bool ->> bool
    it "parses pi-bound nested unrefined types" $
      p "x : Bool -> y : Int -> Bool" ~~> "x".:bool ->> ("y".:int ->> bool)
    it "parses pi-bound nested unrefined types in parens" $
      p "(x : Bool -> y : Int -> Bool) -> Bool" ~~> ("x".:bool ->> ("y".:int ->> bool)) --> bool

-- Some helpers to make tests a tad more pleasant
infixr 0 -->
(-->) :: Ty -> Ty -> Ty
a --> b = TyArrow $ ArrowTy Nothing a b

infixr 2 ->>
(->>) :: Ty -> Ty -> VarName -> Ty
(->>) a b name = TyArrow $ ArrowTy (Just name) a b

infixr 1 .:
(.:) :: a -> (a -> b) -> b
a .: f = f a

bool, int :: Ty
bool = TyBase $ RefinedBaseTy TBool trueRefinement
int = TyBase $ RefinedBaseTy TInt trueRefinement

intLeqLenArr, intGe0 :: Ty
intLeqLenArr = TyBase $ RefinedBaseTy TInt $ Refinement [AR ROpLeq (RArgVarLen "arr")]
intGe0 = TyBase $ RefinedBaseTy TInt $ Refinement [AR ROpGe RArgZero]

intLe :: VarName -> Ty
intLe var = TyBase $ RefinedBaseTy TInt $ Refinement [AR ROpLe (RArgVar var)]
