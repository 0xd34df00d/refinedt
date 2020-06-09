module Main where

import Data.Void
import System.Environment
import Text.Megaparsec hiding (State)

import Toy.Language.Compiler
import Toy.Language.Parser.Decl
import Toy.Language.Syntax.Decls

parseFunDecl :: String -> FunSig
parseFunDecl str = either (error . errorBundlePretty) id parsed
  where
   parsed = runParser (funDecl <* eof) "" str :: Either (ParseErrorBundle String Void) FunSig

main :: IO ()
main = do
  args <- getArgs
  case args of
       ("compileTy" : decls) -> mapM_ putStrLn $ compileFunSig . parseFunDecl <$> decls
       _ -> putStrLn "Unrecognized arguments"
