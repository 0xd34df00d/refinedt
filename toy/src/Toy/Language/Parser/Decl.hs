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
import Toy.Language.Syntax.Decls

funDecl :: ToyMonad e s m => m FunSig
funDecl = do
  funName <- lexeme' identifier
  void $ lsymbol ":"
  funTy <- ty
  pure FunSig { .. }

funDef :: ToyMonad e s m => m FunDef
funDef = funDefNamed identifier

funDefNamed :: ToyMonad e s m => m String -> m FunDef
funDefNamed funNameParser = do
  funName <- lexeme' funNameParser
  funArgs <- many varName
  void $ lstring "="
  funBody <- term
  pure FunDef { .. }

term :: ToyMonad e s m => m Term
term = foldl1 TApp <$> (tbinOp <|> atom) `sepBy1` lexSpace
  where
    tbinOp = try $ TBinOp <$> atom <*> binOp <*> atom
    atom = choice $ try <$> subAtoms
    subAtoms = [ TName <$> varName
               , TInteger <$> lexeme' decimal
      , uncurry3 TIfThenElse <$> tIfThenElse
               , parens term
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

binOp :: ToyMonad e s m => m BinOp
binOp = parseTable [ ("+", BinOpPlus)
                   , ("-", BinOpMinus)
                   , (">", BinOpGt)
                   , ("<", BinOpLt)
                   ]
