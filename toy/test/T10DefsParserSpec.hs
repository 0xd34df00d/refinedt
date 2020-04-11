{-# LANGUAGE OverloadedStrings #-}

module T10DefsParserSpec(spec) where

import Test.Hspec

import Toy.Language.Parser.Decl
import Toy.Language.Syntax.Decls

import TestUtils

spec :: Spec
spec =
  describe "Parsing basic fundefs" $ let p = parse' funDef in do
    it "parses identity function" $
      p "id x = x" ~~> FunDef "id" ["x"] nx
    it "parses application" $
      p "dot x y = x y" ~~> FunDef "dot" ["x", "y"] (nx `TApp` ny)
    it "parses n-ary application" $
      p "f x y z = x y z" ~~> FunDef "f" ["x", "y", "z"] (nx `TApp` ny `TApp` nz)
    it "parses ops" $ do
      p "f x y = x > y" ~~> FunDef "f" ["x", "y"] (nx .>. ny)
      p "add x y = x + y" ~~> FunDef "add" ["x", "y"] (nx .+. ny)
    it "parses nested ops" $
      p "add x y z = x + y + z" ~~> FunDef "add" ["x", "y", "z"] ((nx .+. ny) .+. nz)
    it "parses parens" $
      p "f x y = x (y x)" ~~> FunDef "f" ["x", "y"] (nx `TApp` (ny `TApp` nx))
    it "parses basic if-then-else" $
      p "f b = if b then b else b" ~~> FunDef "f" ["b"] (TIfThenElse nb nb nb)
    it "parses more interesting if-then-else" $
      p "max x y = if x > y then x else y" ~~> FunDef "max" ["x", "y"]
                                                  (TIfThenElse (nx .>. ny) nx ny)
    it "parses nested if-then-else" $
      p "max x y z = if x > y then if x > z then x else z else if y > z then y else z"
                                           ~~> FunDef "max" ["x", "y", "z"]
                                                  (TIfThenElse (nx .>. ny)
                                                    (TIfThenElse (nx .>. nz) nx nz)
                                                    (TIfThenElse (ny .>. nz) ny nz))
    it "parses ops and nested apps" $
      p "f x y = x y + y" ~~> FunDef "f" ["x", "y"] ((nx `TApp` ny) .+. ny)

nb, nx, ny, nz :: Term
nb = TName "b"
nx = TName "x"
ny = TName "y"
nz = TName "z"

(.>.), (.+.) :: Term -> Term -> Term
t1 .>. t2 = TBinOp t1 BinOpGt t2
t1 .+. t2 = TBinOp t1 BinOpPlus t2
