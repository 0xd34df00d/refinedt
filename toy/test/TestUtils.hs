module TestUtils where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Loops
import Data.Bifunctor
import Data.Char
import Data.Either
import Data.Void
import Test.Hspec
import Text.Megaparsec
import Text.SExpression

import Idris.IdeModeClient
import Toy.Language.Parser
import Toy.Language.Syntax.Decls

parse' :: Parsec Void String a -> String -> Either ErrorMsg a
parse' p = first (ErrorMsg . errorBundlePretty) . runParser (p <* eof) ""

newtype ErrorMsg = ErrorMsg { getErrorMsg :: String } deriving (Eq)

instance Show ErrorMsg where
  show = getErrorMsg

infixr 0 ~~>
(~~>) :: (Show err, Eq err, Show r, Eq r) => Either err r -> r -> Expectation
parseRes ~~> expected = parseRes `shouldBe` Right expected

trimIndentation :: String -> String
trimIndentation str = case flt $ lines str of
                           (l:ls) -> unlines $ flt $ drop (countLeading l) <$> l:ls
                           _ -> str
  where
    countLeading = length . takeWhile isSpace
    flt = filter $ not . null

testWithIdris :: SpecWith IdrisHandle -> SpecWith ()
testWithIdris = parallel . beforeAll startIdris . afterAll stopIdris

testParseFunWithCtx :: String -> IO ([FunSig], (FunSig, FunDef))
testParseFunWithCtx str =
  case parseRes of
       Right r -> pure r
       _ -> do
          parseRes `shouldSatisfy` isRight
          error "expected Right"
  where
    parseRes = parse' funWithCtx $ trimIndentation str

isReturn :: SExpr -> Bool
isReturn (List (Atom ":return" : _)) = True
isReturn _ = False

isOkReply :: SExpr -> Bool
isOkReply (List [Atom ":return", List (Atom ":ok" : _), _]) = True
isOkReply _ = False

testIdrisFile :: MonadIO m => File -> IdrisClientT m ()
testIdrisFile file = do
  sendCommand $ loadFile file
  reply <- iterateUntil isReturn readReply
  unless (isOkReply reply) $ dumpFile file
  liftIO $ reply `shouldSatisfy` isOkReply
