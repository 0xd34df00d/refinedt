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
  funBody <- expr
  pure FunDef { .. }

expr :: ToyMonad e s m => m Expr
expr = choice $ try <$> eparsers
  where
    eparsers = [ EName <$> varName
               , EInt <$> lexeme' decimal
               , EOperator <$> op
       , uncurry EApp <$> eapp
      , uncurry3 EIfThenElse <$> eIfThenElse
               ]

eapp :: ToyMonad e s m => m (Expr, Expr)
eapp = do
  lhs <- expr
  rhs <- expr
  pure (lhs, rhs)

eIfThenElse :: ToyMonad e s m => m (Expr, Expr, Expr)
eIfThenElse = do
  void $ lstring "if"
  eif <- expr
  void $ lstring "then"
  ethen <- expr
  void $ lstring "else"
  eelse <- expr
  pure (eif, ethen, eelse)

op :: ToyMonad e s m => m Op
op = parseTable [ ("+", OpPlus)
                , ("-", OpMinus)
                , (">", OpGt)
                , ("<", OpLt)
                ]
