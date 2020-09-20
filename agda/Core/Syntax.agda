module Core.Syntax where

open import Agda.Builtin.String

data Sort : Set where
  ⋆ : Sort
  □ : Sort

record Var : Set where
  constructor MkVar
  field
    var : String

data CExpr : Set where
  CVar  : (var : Var) → CExpr
  CPi   : (var : Var) → (ε₁ ε₂ : CExpr) → CExpr
  CLam  : (var : Var) → (ε₁ ε₂ : CExpr) → CExpr
  CApp  : (ε₁ ε₂ : CExpr) → CExpr
  Cunit : CExpr
  CUnit : CExpr
