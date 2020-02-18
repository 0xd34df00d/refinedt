{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings, RecordWildCards #-}

module Toy.Language.Parser where

import Control.Monad
import Control.Monad.State.Strict
import Data.Char
import Data.Default
import Data.Functor
import Data.String
import GHC.Exts
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer as ML

import Toy.Language.Types

type ToyMonad e s m = (MonadParsec e s m,
                       Token s ~ Char, IsString (Tokens s),
                       IsList (Tokens s), Item (Tokens s) ~ Char,
                       MonadState ParseState m)

parseTy :: ToyMonad e s m => m Ty
parseTy = TyArrow <$> try parseArrow
      <|> parens parseTy
      <|> TyBase <$> parseBaseRT

newtype ParseState = ParseState
  { lastArrowPos :: Maybe SourcePos
  } deriving (Eq, Ord, Show)

instance Default ParseState where
  def = ParseState Nothing

parseArrow :: ToyMonad e s m => m ArrowTy
parseArrow = do
  let piVarName = Nothing

  curPos <- getSourcePos
  prevPos <- gets lastArrowPos
  guard $ Just curPos /= prevPos

  modify' $ \st -> st { lastArrowPos = Just curPos }

  domTy <- parseTy
  void $ lstring "->"
  codTy <- parseTy
  pure $ ArrowTy { .. }

parseBaseRT :: ToyMonad e s m => m RefinedBaseTy
parseBaseRT = try refinedTy <|> implicitTrue
  where
    implicitTrue = RefinedBaseTy <$> parseBaseTy <*> pure trueRefinement
    refinedTy = do
      void $ lstring "{"
      void $ lstring "ν"
      void $ lstring ":"
      baseType <- parseBaseTy
      void $ lstring "|"
      refinement <- parseRefinement
      void $ lstring "}"
      pure $ RefinedBaseTy { .. }

parseRefinement :: ToyMonad e s m => m Refinement
parseRefinement = Refinement <$> parseAtomicRefinement `sepBy1` lstring "&"

parseAtomicRefinement :: ToyMonad e s m => m AtomicRefinement
parseAtomicRefinement = lstring "ν" >> AR <$> parseTable ops <*> args
  where
    ops = [ ("<=", ROpLeq), ("<", ROpLe), ("=", ROpEq), ("/=", ROpNEq), (">=", ROpGeq), (">", ROpGe) ]
    args = choice [ lstring "0" $> RArgZero
                  , lstringSpace "len" >> RArgVarLen <$> parseVarName
                  , RArgVar <$> parseVarName
                  ]

parseBaseTy :: ToyMonad e s m => m BaseTy
parseBaseTy = lstring "Bool" $> TBool
          <|> lstring "Int" $> TInt

parseVarName :: ToyMonad e s m => m VarName
parseVarName = lexeme' $ VarName . toList <$> takeWhile1P (Just "variable") isLetter

-- Utils

parseTable :: ToyMonad e s m => [(Tokens s, a)] -> m a
parseTable table = choice [ lstring str $> op | (str, op) <- table ]

lexeme' :: ToyMonad e s m => m a -> m a
lexeme' = lexeme lexSpace

lstring :: ToyMonad e s m => Tokens s -> m (Tokens s)
lstring = try . lexeme' . string

lstringSpace :: ToyMonad e s m => Tokens s -> m (Tokens s)
lstringSpace s = try $ lexeme' $ string s <* space1

lsymbol :: ToyMonad e s m => Tokens s -> m (Tokens s)
lsymbol = ML.symbol lexSpace

parens :: ToyMonad e s m => m a -> m a
parens = between (lsymbol "(") (lsymbol ")")

lexSpace :: ToyMonad e s m => m ()
lexSpace = ML.space space1 empty empty
