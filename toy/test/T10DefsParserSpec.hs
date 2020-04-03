{-# LANGUAGE OverloadedStrings #-}

module T10DefsParserSpec(spec) where

import Test.Hspec

import Toy.Language.Parser.Decl
import Toy.Language.Syntax.Decl

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
    it "parses ops" $
      p "f x y = x > y" ~~> FunDef "f" ["x", "y"] (TBinOp nx BinOpGt ny)
    it "parses parens" $
      p "f x y = x (y x)" ~~> FunDef "f" ["x", "y"] (nx `TApp` (ny `TApp` nx))
    it "parses basic if-then-else" $
      p "f b = if b then b else b" ~~> FunDef "f" ["b"] (TIfThenElse nb nb nb)
    it "parses more interesting if-then-else" $
      p "max x y = if x > y then x else y" ~~> FunDef "max" ["x", "y"]
                                                  (TIfThenElse (TBinOp nx BinOpGt ny) nx ny)

nb, nx, ny, nz :: Term
nb = TName "b"
nx = TName "x"
ny = TName "y"
nz = TName "z"
