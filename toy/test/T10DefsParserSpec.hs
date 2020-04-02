{-# LANGUAGE OverloadedStrings #-}

module T10DefsParserSpec(spec) where

import Test.Hspec

import Toy.Language.Parser.Decl
import Toy.Language.Syntax.Decl

import TestUtils

spec :: Spec
spec = do
  describe "Parsing basic fundefs" $ let p = parse' funDef in do
    it "parses identity function" $ p "id x = x" ~~> FunDef "id" ["x"] (EName "x")
