module Misc.Util where

import Data.List

parens :: String -> String
parens str
  | ' ' `notElem` str = str
  | head str == '(' && last str == ')' && isBalanced (init $ tail str) = str
  | otherwise = "(" <> str <> ")"
  where
    isBalanced = (\(n, b) -> b && n == 0) . foldl' f (0 :: Int, True)
    f (0, _) ')' = (0, False)
    f (n, b) '(' = (n + 1, b)
    f (n, b) ')' = (n - 1, b)
    f (n, b) _ = (n, b)
