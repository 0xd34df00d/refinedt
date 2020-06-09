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
  sig@FunSig { .. } <- funSig <* eol
  let nameParser = string (fromString funName) $> funName
  def <- funDefNamed nameParser <* optional eol
  pure (sig, def)

funWithCtx :: ToyMonad e s m => m ([FunSig], (FunSig, FunDef))
funWithCtx = do
  sigs <- some $ try $ funSig <* some eol
  let sig@FunSig { .. } = last sigs
  let nameParser = string (fromString funName) $> funName
  def <- funDefNamed nameParser <* optional eol
  pure (init sigs, (sig, def))
