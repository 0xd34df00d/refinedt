module TestUtils where

import Data.Bifunctor
import Data.Void
import Test.Hspec
import Text.Megaparsec

parse' :: Parsec Void String a -> String -> Either ErrorMsg a
parse' p = first (ErrorMsg . errorBundlePretty) . runParser (p <* eof) ""

newtype ErrorMsg = ErrorMsg { getErrorMsg :: String } deriving (Eq)

instance Show ErrorMsg where
  show = getErrorMsg

infixr 0 ~~>
(~~>) :: (Show err, Eq err, Show r, Eq r) => Either err r -> r -> Expectation
parseRes ~~> expected = parseRes `shouldBe` Right expected
