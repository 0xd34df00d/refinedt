{-# LANGUAGE DuplicateRecordFields, RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}

module Toy.Language.Syntax.Decls where

import Control.Monad.Identity

import Toy.Language.Syntax.Common
import Toy.Language.Syntax.Terms
import Toy.Language.Syntax.Types

data FunSig = FunSig
  { funName :: String
  , funTy :: Ty
  } deriving (Eq, Ord, Show)

data FunDefT a = FunDef
  { funName :: String
  , funArgs :: [VarName]
  , funBody :: TermT a
  } deriving (Eq, Ord, Show, Functor)

type FunDef = FunDefT ()
type TypedFunDef = FunDefT Ty

data DeclT a = Decl
  { declSig :: FunSig
  , declDef :: Maybe (FunDefT a)
  } deriving (Eq, Ord, Show, Functor)

type Decl = DeclT ()

onFunBody :: (TermT a -> TermT b) -> FunDefT a -> FunDefT b
onFunBody f = runIdentity . onFunBodyM (pure . f)

onFunBodyM :: Functor m => (TermT a -> m (TermT b)) -> FunDefT a -> m (FunDefT b)
onFunBodyM f FunDef { .. } = (\funBody' -> FunDef { funBody = funBody', .. }) <$> f funBody
