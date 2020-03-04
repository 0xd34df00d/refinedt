module Toy.Language.Syntax.Decl where

import Toy.Language.Syntax.Types

data FunDecl = FunDecl
  { funName :: String
  , funTy :: Ty
  } deriving (Eq, Ord, Show)