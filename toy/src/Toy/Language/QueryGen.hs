module Toy.Language.QueryGen where

import Toy.Language.Syntax.Decls
import Toy.Language.Syntax.Types

data Query = Query
  { antecedent :: Refinement
  , consequent :: Refinement
  } deriving (Eq, Ord, Show)

data QAnnotation = QAnnotation
  { tyPart :: Ty
  , queryPart :: Query
  } deriving (Eq, Ord, Show)

type QTerm = TermT QAnnotation
type QFunDef = FunDefT QAnnotation

genQueries :: TypedTerm -> QTerm
genQueries = undefined
