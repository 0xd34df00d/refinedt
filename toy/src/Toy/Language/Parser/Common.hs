{-# LANGUAGE TypeFamilies, FlexibleContexts #-}

module Toy.Language.Parser.Common where

import Toy.Language.Syntax.Types
import Toy.Language.Parser.Util

varName :: ToyMonad e s m => m VarName
varName = lexeme' $ VarName <$> identifier
