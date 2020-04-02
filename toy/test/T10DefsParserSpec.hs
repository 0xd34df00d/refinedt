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
    it "parses ops" $
      p "f x y = x > y" ~~> FunDef "f" ["x", "y"] (TBinOp nx BinOpGt ny)
    it "parses parens" $
      p "f x y = x (y x)" ~~> FunDef "f" ["x", "y"] (nx `TApp` (ny `TApp` nx))

nx, ny :: Term
nx = TName "x"
ny = TName "y"
