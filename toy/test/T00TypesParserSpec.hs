{-# LANGUAGE OverloadedStrings #-}

module T00TypesParserSpec(spec) where

import Test.Hspec

import Toy.Language.Parser.Ty
import Toy.Language.Syntax.Common
import Toy.Language.Syntax.Terms
import Toy.Language.Syntax.Terms.Sugar
import Toy.Language.Syntax.Types

import TestUtils

vRefinement :: [AtomicRefinement] -> Maybe Refinement
vRefinement = Just . Refinement v

spec :: Spec
spec = do
  describe "Parsing base refined types" $ let p = parse' baseRT in do
    it "parses unrefined type" $
      p "Bool" ~~> RefinedBaseTy TBool trueRefinement
    it "parses refined type with var" $
      p "{ v : Bool | v < x }" ~~> RefinedBaseTy TBool $ vRefinement [AR $ v |<| "x"]
    it "parses refined type with zero" $
      p "{ v : Bool | v <= 0 }" ~~> RefinedBaseTy TBool $ vRefinement [AR $ v |<=| ti 0]
    it "parses refined type with len" $
      p "{ v : Bool | v >= len arr }" ~~> RefinedBaseTy TBool $ vRefinement [AR $ v |>=| len "arr"]
    it "parses refined type without spaces" $
      p "{v:Bool|v>=len arr}" ~~> RefinedBaseTy TBool $ vRefinement [AR $ v |>=| len "arr"]
    it "parses refined type with var name starting with len" $
      p "{ v : Bool | v >= lenarr }" ~~> RefinedBaseTy TBool $ vRefinement [AR $ v |>=| "lenarr"]
  describe "Parsing with conjunctions" $ let p = parse' baseRT in do
    it "parses types with conjunctions 1" $
      p "{ v : Bool | v < x & v > 0 }" ~~> RefinedBaseTy TBool $ vRefinement [AR $ v |<| "x", AR $ v |>| ti 0]
    it "parses types with conjunctions 2" $
      p "{ v : Bool | v < x & v < len arr }" ~~> RefinedBaseTy TBool $ vRefinement [AR $ v |<| "x", AR $ v |<| len "arr"]
  describe "Parsing arrows" $ let p = parse' ty in do
    it "still parses base types" $
      p "{ v : Bool | v >= len arr }" ~~> TyBase $ RefinedBaseTy TBool $ vRefinement [AR $ v |>=| len "arr"]
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
      p "{ v : Int | v <= len arr } -> { v : Int | v > 0 }" ~~> intLeqLenArr --> intGe0
    it "parses simple arrows in parens" $
      p "({ v : Int | v <= len arr } -> { v : Int | v > 0 })" ~~> intLeqLenArr --> intGe0
    it "parses nested arrows" $
      p "{ v : Int | v <= len arr } -> { v : Int | v < var1 } -> { v : Int | v < var2 }"
        ~~> intLeqLenArr --> intLe "var1" --> intLe "var2"
    it "parses nested arrows with parens" $
      p "({ v : Int | v <= len arr } -> { v : Int | v < var1 }) -> { v : Int | v < var2 }"
        ~~> (intLeqLenArr --> intLe "var1") --> intLe "var2"
  describe "Parsing arrows and pi-bound variables" $ let p = parse' ty in do
    it "parses pi-bound unrefined types" $
      p "(x : Bool) -> Bool" ~~> "x".:bool ->> bool
    it "parses pi-bound nested unrefined types" $
      p "(x : Bool) -> (y : Int) -> Bool" ~~> "x".:bool ->> ("y".:int ->> bool)
    it "parses pi-bound nested unrefined types in parens" $
      p "((x : Bool) -> (y : Int) -> Bool) -> Bool" ~~> ("x".:bool ->> ("y".:int ->> bool)) --> bool
    it "parses pi-bound nested unrefined types in pi-bound parens" $
      p "(f : (x : Bool) -> (y : Int) -> Bool) -> Bool" ~~> "f".:("x".:bool ->> ("y".:int ->> bool)) ->> bool
  describe "Parsing arrows, refinements and pi-bound variables" $ let p = parse' ty in do
    it "parses pi-bound refined types" $
      p "(x : { v : Int | v <= len arr }) -> { v : Int | v >= 0 & v < x }"
        ~~> "x".:intLeqLenArr ->> intBetween0andX
    it "parses pi-bound nested refined types" $
      p "(x : { v : Int | v <= len arr }) -> (y : { v : Int | v > 0 }) -> { v : Int | v >= 0 & v < x }"
        ~~> "x".:intLeqLenArr ->> ("y".:intGe0 ->> intBetween0andX)
    it "parses pi-bound nested refinement types in pi-bound parens" $
      p "(f : (x : { v : Int | v <= len arr }) -> { v : Int | v > 0 }) -> { v : Int | v >= 0 & v < x }"
        ~~> "f".:("x".:intLeqLenArr ->> intGe0) ->> intBetween0andX

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

intLeqLenArr, intGe0, intBetween0andX :: Ty
intLeqLenArr = TyBase $ RefinedBaseTy TInt $ vRefinement [AR $ v |<=| len "arr"]
intGe0 = TyBase $ RefinedBaseTy TInt $ vRefinement [AR $ v |>| ti 0]
intBetween0andX = TyBase $ RefinedBaseTy TInt $ vRefinement [AR $ v |>=| ti 0, AR $ v |<| "x"]

intLe :: Term -> Ty
intLe var = TyBase $ RefinedBaseTy TInt $ vRefinement [AR $ v |<| var]
