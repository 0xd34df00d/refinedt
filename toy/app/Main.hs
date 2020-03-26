module Main where

import Data.Void
import System.Environment
import Text.Megaparsec hiding (State)

import Toy.Language.Compiler
import Toy.Language.Parser.Decl
import Toy.Language.Syntax.Decl

parseFunDecl :: String -> FunDecl
parseFunDecl str = either (error . errorBundlePretty) id parsed
  where
   parsed = runParser (funDecl <* eof) "" str :: Either (ParseErrorBundle String Void) FunDecl

main :: IO ()
main = do
  args <- getArgs
  case args of
       ["compileTy", funDeclStr] -> putStrLn $ compileFunDecl $ parseFunDecl funDeclStr
       _ -> putStrLn "Unrecognized arguments"
