module Toy.Language.QueryGen where

import Toy.Language.Syntax.Decls
import Toy.Language.Syntax.Types

-- The intrinsic refinement characterizes the structure of the term and doesn't need to be checked but can be assumed.
-- The VC proposition is whatever needs to hold for that specific term to type check (not including its subterms).
data QAnnotation = QAnnotation
  { intrinsicProp :: Refinement
  , tyAnn :: Ty
  } deriving (Eq, Ord, Show)

type QTerm = TermT QAnnotation
type QFunDef = FunDefT QAnnotation

emptyQAnn :: Refinement -> TypedTerm -> QTerm
emptyQAnn = fmap . QAnnotation

genQueries :: TypedTerm -> QTerm
genQueries t@(TName ty _) = emptyQAnn (tyRefinement' ty) t
genQueries (TInteger ty n) = TInteger (QAnnotation refinement ty) n
  where
    refinement = Refinement [AR ROpEq $ RArgInt n]
