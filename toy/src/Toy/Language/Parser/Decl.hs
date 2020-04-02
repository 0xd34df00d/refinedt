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
term = choice $ try <$> eparsers
  where
    eparsers = [ TName <$> varName
               , TInteger <$> lexeme' decimal
               , TOperator <$> op
       , uncurry TApp <$> tapp
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
  eif <- term
  void $ lstring "then"
  ethen <- term
  void $ lstring "else"
  eelse <- term
  pure (eif, ethen, eelse)

op :: ToyMonad e s m => m Op
op = parseTable [ ("+", OpPlus)
                , ("-", OpMinus)
                , (">", OpGt)
                , ("<", OpLt)
                ]
