{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings, RecordWildCards, TupleSections #-}

module Toy.Language.Parser.Ty
( ty
, baseRT
) where

import Control.Monad
import Data.List.Extra
import Data.String
import Text.Megaparsec
import Text.Megaparsec.Char.Lexer

import Toy.Language.Syntax
import Toy.Language.Syntax.Terms.Sugar
import Toy.Language.Parser.Common
import Toy.Language.Parser.Util

ty :: ToyMonad e s m => m Ty
ty = TyArrow <$> try arrow
 <|> arrowLHS

arrowLHS :: ToyMonad e s m => m Ty
arrowLHS = parens ty <|> TyBase <$> baseRT

arrow :: ToyMonad e s m => m ArrowTy
arrow = do
  (piVarName, domTy) <- boundLHS <|> unboundLHS
  void $ lstring "->"
  codTy <- ty
  pure $ ArrowTy { .. }
  where
    unboundLHS = (Nothing,) <$> arrowLHS
    boundLHS = try $ parens $ do
      piVarName <- Just <$> varName <* lstring ":"
      domTy <- ty
      pure (piVarName, domTy)

baseRT :: ToyMonad e s m => m RefinedBaseTy
baseRT = try refinedTy <|> implicitTrue
  where
    implicitTrue = RefinedBaseTy <$> baseTy <*> pure trueRefinement
    refinedTy = do
      void $ lstring "{"
      void $ lstring "v"
      void $ lstring ":"
      baseType <- baseTy
      void $ lstring "|"
      baseTyRefinement <- Just <$> refinement
      void $ lstring "}"
      pure $ RefinedBaseTy { .. }

-- TODO support custom refinement vars
refinement :: ToyMonad e s m => m Refinement
refinement = Refinement "v" <$> atomicRefinement `sepBy1` lstring "&"

atomicRefinement :: ToyMonad e s m => m AtomicRefinement
atomicRefinement = do
  void $ lstring "v"
  (\op arg -> AR $ TBinOp () v op arg) <$> parseTable ops <*> args
  where
    ops = [ ("<=", BinOpLeq), ("<", BinOpLt), ("=", BinOpEq), ("/=", BinOpNEq), (">=", BinOpGeq), (">", BinOpGt) ]
    args = choice [ TInteger () <$> lexeme' decimal
                  , lstringSpace "len" >> TApp () "len" . TName ()  <$> varName
                  , TName () <$> varName
                  ]

baseTy :: ToyMonad e s m => m BaseTy
baseTy = parseTable [ (fromString str, bty)
                    | bty <- enumerate
                    , let str = tail $ show bty
                    ]
