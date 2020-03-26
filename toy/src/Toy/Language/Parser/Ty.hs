{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings, RecordWildCards, TupleSections #-}

module Toy.Language.Parser.Ty
( ty
, baseRT
) where

import Control.Monad
import Data.Functor
import Text.Megaparsec

import Toy.Language.Parser.Util
import Toy.Language.Syntax.Types

ty :: ToyMonad e s m => m Ty
ty = TyArrow <$> try arrow
 <|> arrowLHS

arrowLHS :: ToyMonad e s m => m Ty
arrowLHS = parens ty <|> TyBase <$> baseRT

arrow :: ToyMonad e s m => m ArrowTy
arrow = do
  (piVarName, domTy) <- boundLHS <|> unboundLHS
  void $ lstring "->"
  codTy <- ty
  pure $ ArrowTy { .. }
  where
    unboundLHS = (Nothing,) <$> arrowLHS
    boundLHS = try $ parens $ do
      piVarName <- Just <$> varName <* lstring ":"
      domTy <- ty
      pure (piVarName, domTy)

baseRT :: ToyMonad e s m => m RefinedBaseTy
baseRT = try refinedTy <|> implicitTrue
  where
    implicitTrue = RefinedBaseTy <$> baseTy <*> pure trueRefinement
    refinedTy = do
      void $ lstring "{"
      void $ lstring "ν"
      void $ lstring ":"
      baseType <- baseTy
      void $ lstring "|"
      baseTyRefinement <- refinement
      void $ lstring "}"
      pure $ RefinedBaseTy { .. }

refinement :: ToyMonad e s m => m Refinement
refinement = Refinement <$> atomicRefinement `sepBy1` lstring "&"

atomicRefinement :: ToyMonad e s m => m AtomicRefinement
atomicRefinement = lstring "ν" >> AR <$> parseTable ops <*> args
  where
    ops = [ ("<=", ROpLeq), ("<", ROpLe), ("=", ROpEq), ("/=", ROpNEq), (">=", ROpGeq), (">", ROpGe) ]
    args = choice [ lstring "0" $> RArgZero
                  , lstringSpace "len" >> RArgVarLen <$> varName
                  , RArgVar <$> varName
                  ]

baseTy :: ToyMonad e s m => m BaseTy
baseTy = lstring "Bool" $> TBool
     <|> lstring "Int" $> TInt
     <|> lstring "IntList" $> TIntList

varName :: ToyMonad e s m => m VarName
varName = lexeme' $ VarName <$> identifier
