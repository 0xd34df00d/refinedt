{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
{-# LANGUAGE RecordWildCards, OverloadedStrings #-}

module Toy.Language.Parser.Decl where

import Data.Functor
import Data.Tuple.Extra
import Text.Megaparsec
import Text.Megaparsec.Char.Lexer

import Toy.Language.Parser.Common
import Toy.Language.Parser.Ty
import Toy.Language.Parser.Util
import Toy.Language.Syntax.Decl

funDecl :: ToyMonad e s m => m FunDecl
funDecl = do
  funName <- lexeme' identifier
  void $ lsymbol ":"
  funTy <- ty
  pure FunDecl { .. }

funDef :: ToyMonad e s m => m FunDef
funDef = do
  funName <- lexeme' identifier
  funArgs <- many varName
  void $ lstring "="
  funBody <- term
  pure FunDef { .. }

term :: ToyMonad e s m => m Term
term = foldl1 TApp <$> atoms `sepBy1` lexSpace
  where
    atoms = choice $ try <$> subAtoms
    subAtoms = [ TName <$> varName
               , TInteger <$> lexeme' decimal
               , TOperator <$> op
      , uncurry3 TIfThenElse <$> tIfThenElse
               ]

tapp :: ToyMonad e s m => m (Term, Term)
tapp = do
  lhs <- term
  rhs <- term
  pure (lhs, rhs)

tIfThenElse :: ToyMonad e s m => m (Term, Term, Term)
tIfThenElse = do
  void $ lstring "if"
  tif <- term
  void $ lstring "then"
  tthen <- term
  void $ lstring "else"
  telse <- term
  pure (tif, tthen, telse)

op :: ToyMonad e s m => m Op
op = parseTable [ ("+", OpPlus)
                , ("-", OpMinus)
                , (">", OpGt)
                , ("<", OpLt)
                ]
