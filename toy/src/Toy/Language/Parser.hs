{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings, RecordWildCards #-}

module Toy.Language.Parser
( ty
, baseRT

, ParseState
) where

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

ty :: ToyMonad e s m => m Ty
ty = TyArrow <$> try arrow
 <|> parens ty
 <|> TyBase <$> baseRT

newtype ParseState = ParseState
  { lastArrowPos :: Maybe SourcePos
  } deriving (Eq, Ord, Show)

instance Default ParseState where
  def = ParseState Nothing

arrow :: ToyMonad e s m => m ArrowTy
arrow = do
  piVarName <- optional $ try $ varName <* lstring ":"

  curPos <- getSourcePos
  prevPos <- gets lastArrowPos
  guard $ Just curPos /= prevPos

  modify' $ \st -> st { lastArrowPos = Just curPos }

  domTy <- ty
  void $ lstring "->"
  codTy <- ty
  pure $ ArrowTy { .. }

baseRT :: ToyMonad e s m => m RefinedBaseTy
baseRT = try refinedTy <|> implicitTrue
  where
    implicitTrue = RefinedBaseTy <$> baseTy <*> pure trueRefinement
    refinedTy = do
      void $ lstring "{"
      void $ lstring "ν"
      void $ lstring ":"
      baseType <- baseTy
      void $ lstring "|"
      baseTyRefinement <- refinement
      void $ lstring "}"
      pure $ RefinedBaseTy { .. }

refinement :: ToyMonad e s m => m Refinement
refinement = Refinement <$> atomicRefinement `sepBy1` lstring "&"

atomicRefinement :: ToyMonad e s m => m AtomicRefinement
atomicRefinement = lstring "ν" >> AR <$> parseTable ops <*> args
  where
    ops = [ ("<=", ROpLeq), ("<", ROpLe), ("=", ROpEq), ("/=", ROpNEq), (">=", ROpGeq), (">", ROpGe) ]
    args = choice [ lstring "0" $> RArgZero
                  , lstringSpace "len" >> RArgVarLen <$> varName
                  , RArgVar <$> varName
                  ]

baseTy :: ToyMonad e s m => m BaseTy
baseTy = lstring "Bool" $> TBool
     <|> lstring "Int" $> TInt

varName :: ToyMonad e s m => m VarName
varName = lexeme' $ VarName <$> identifier

identifier :: ToyMonad e s m => m String
identifier = do
  firstLetter <- letterChar
  rest <- takeWhileP (Just "variable") isAlphaNum
  pure $ firstLetter : toList rest

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
