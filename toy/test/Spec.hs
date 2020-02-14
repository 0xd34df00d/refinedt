import Data.Void
import Test.Hspec
import Text.Megaparsec

import Toy.Language.Parser
import Toy.Language.Types

parse' :: Parsec Void String a -> String -> Either (ParseErrorBundle String Void) a
parse' p = parse p ""

main :: IO ()
main = hspec $
  describe "Parsing base refined types" $ do
    it "parses unrefined type" $
      parse' parseBaseRT "Bool" `shouldBe` Right (RefinedBaseTy TBool trueRefinement)
