{-# LANGUAGE TypeFamilies, FlexibleContexts #-}

module Toy.Language.Parser.Common where

import Toy.Language.Parser.Util
import Toy.Language.Syntax.Common

varName :: ToyMonad e s m => m VarName
varName = lexeme' $ VarName <$> identifier
