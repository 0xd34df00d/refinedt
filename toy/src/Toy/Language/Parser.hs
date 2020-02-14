{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Toy.Language.Parser where

import Data.Char
import Data.Functor
import Data.String
import GHC.Exts
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer as ML

import Toy.Language.Types

type ToyMonad e s m = (MonadParsec e s m,
                       Token s ~ Char, IsString (Tokens s),
                       IsList (Tokens s), Item (Tokens s) ~ Char)

tyParser :: ToyMonad e s m => m Ty
tyParser = undefined

parseBaseRT :: ToyMonad e s m => m RefinedBaseTy
parseBaseRT = undefined

parseAtomicRefinement :: ToyMonad e s m => m AtomicRefinement
parseAtomicRefinement = undefined

parseBaseTy :: ToyMonad e s m => m BaseTy
parseBaseTy = lstring "Bool" $> TBool
          <|> lstring "Int" $> TInt

parseVarName :: ToyMonad e s m => m VarName
parseVarName = VarName . toList <$> takeWhile1P (Just "variable") isLetter

lexeme' :: ToyMonad e s m => m a -> m a
lexeme' = lexeme $ ML.space space1 empty empty

lstring :: ToyMonad e s m => Tokens s -> m (Tokens s)
lstring = lexeme' . string
