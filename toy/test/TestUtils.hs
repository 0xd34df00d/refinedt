module TestUtils where

import Data.Bifunctor
import Data.Void
import Text.Megaparsec

parse' :: Parsec Void String a -> String -> Either ErrorMsg a
parse' p = first (ErrorMsg . errorBundlePretty) . runParser (p <* eof) ""

newtype ErrorMsg = ErrorMsg { getErrorMsg :: String } deriving (Eq)

instance Show ErrorMsg where
  show = getErrorMsg

