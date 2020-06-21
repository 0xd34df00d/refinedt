module Misc.Pretty where

class Pretty a where
  pretty :: a -> String

instance Pretty () where
  pretty _ = ""
