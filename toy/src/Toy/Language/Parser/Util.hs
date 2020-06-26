{-# LANGUAGE ConstraintKinds, TypeFamilies, FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings, TransformListComp #-}

module Toy.Language.Parser.Util where

import Control.Monad
import Data.Char
import Data.Functor
import Data.List.Extra
import Data.String
import GHC.Exts
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer as ML

type ToyMonad e s m = (MonadParsec e s m,
                       Token s ~ Char, IsString (Tokens s),
                       IsList (Tokens s), Item (Tokens s) ~ Char)

identifier :: ToyMonad e s m => m String
identifier = do
  firstLetter <- letterChar
  rest <- takeWhileP (Just "variable") $ \t -> isAlphaNum t || t == '\''
  let res = firstLetter : toList rest
  when (res `elem` ["if", "then", "else"]) $ unexpected $ Label $ fromList $ "keyword \"" <> res <> "\""
  pure res

-- Utils

parseTable :: ToyMonad e s m => [(Tokens s, a)] -> m a
parseTable table = choice [ lstring str $> op
                          | (str, op) <- table
                          , then sortOn by negate (length $ toList str)
                          ]

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
lexSpace = ML.space myspace lineComments empty
  where
    myspace = void $ takeWhile1P (Just "white space") $ \c -> c /= '\n' && isSpace c
    lineComments = skipLineComment "--"
