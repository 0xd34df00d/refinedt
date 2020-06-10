module Main where

import Data.Bifunctor
import Data.Void
import System.Environment
import Text.Megaparsec hiding (State)

import Toy.Language.Compiler
import Toy.Language.Parser
import Toy.Language.Syntax.Decls

parseFunDecls :: String -> Either String [Decl]
parseFunDecls str = first errorBundlePretty parsed
  where
   parsed = runParser (decls <* eof) "" str :: Either (ParseErrorBundle String Void) [Decl]

main :: IO ()
main = do
  args <- getArgs
  case args of
       ["transpile", filename] -> do
          contents <- readFile filename
          case parseFunDecls contents of
               Left err -> putStrLn $ "Parse error:\n" <> err
               Right ds -> putStr $ compileDecls ds
       _ -> putStrLn "Unrecognized arguments"
