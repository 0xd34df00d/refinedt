{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Toy.Language.Syntax.Common where

import Data.Data
import Data.Hashable
import Data.String

newtype VarName = VarName { getName :: String } deriving (Eq, Ord, Show, IsString, Hashable, Data)

