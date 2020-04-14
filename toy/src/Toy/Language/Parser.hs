{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}

module Toy.Language.Parser where

import Data.Functor
import Data.String
import Text.Megaparsec
import Text.Megaparsec.Char

import Toy.Language.Parser.Decl
import Toy.Language.Parser.Util
import Toy.Language.Syntax.Decls

fun :: ToyMonad e s m => m (FunSig, FunDef)
fun = do
  sig@FunSig { .. } <- funDecl <* eol
  let nameParser = string (fromString funName) $> funName
  def <- funDefNamed nameParser <* optional eol
  pure (sig, def)

funWithCtx :: ToyMonad e s m => m ([FunSig], (FunSig, FunDef))
funWithCtx = do
  decls <- some $ try $ funDecl <* some eol
  let sig@FunSig { .. } = last decls
  let nameParser = string (fromString funName) $> funName
  def <- funDefNamed nameParser <* optional eol
  pure (init decls, (sig, def))
