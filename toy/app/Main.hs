module Main where

import Control.Monad.IO.Class
import Data.Void
import System.Environment
import Text.Megaparsec hiding (State)

import Toy.Language.Compiler
import Toy.Language.Parser.Decl
import Toy.Language.Syntax.Decls

import Z3.Monad

parseFunDecl :: String -> FunSig
parseFunDecl str = either (error . errorBundlePretty) id parsed
  where
   parsed = runParser (funDecl <* eof) "" str :: Either (ParseErrorBundle String Void) FunSig

script :: Int -> Z3 ()
script n = do
  v <- mkFreshIntVar "v"
  zero <- mkInteger 0
  n' <- mkInteger $ fromIntegral n
  context <- sequence [v `mkGe` zero, v `mkLt` n']
  assert =<< mkAnd context
  check >>= liftIO . print
  pure ()

main :: IO ()
main = do
  args <- getArgs
  case args of
       ("compileTy" : decls) -> mapM_ putStrLn $ compileFunSig . parseFunDecl <$> decls
       ["z3", n] -> evalZ3 (script $ read n) >>= print
       _ -> putStrLn "Unrecognized arguments"
