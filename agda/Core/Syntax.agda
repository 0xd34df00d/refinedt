module Core.Syntax where

open import Agda.Builtin.String
open import Data.Nat.Base public
open import Data.Fin public using (Fin)
open import Data.Vec.Base

data Sort : Set where
  ⋆ : Sort
  □ : Sort

record Var : Set where
  constructor MkVar
  field
    var : String

ADTCons : ℕ → Set
CaseBranches : ℕ → Set

record CaseBranch : Set

data CExpr : Set where
  CVar  : (var : Var) → CExpr
  CPi   : (var : Var) → (ε₁ ε₂ : CExpr) → CExpr
  CLam  : (var : Var) → (ε₁ ε₂ : CExpr) → CExpr
  CApp  : (ε₁ ε₂ : CExpr) → CExpr
  Cunit : CExpr
  CUnit : CExpr
  CADT  : ∀ {n} → (cons : ADTCons n) → CExpr
  CCon  : ∀ {n} → (idx : Fin n) → (body : CExpr) → (cons : ADTCons n) → CExpr
  CCase : ∀ {n} → (scrut : CExpr) → (branches : CaseBranches n) → CExpr

ADTCons = Vec CExpr
CaseBranches = Vec CaseBranch

record CaseBranch where
  constructor MkCaseBranch
  inductive
  field
    x : Var
    π : Var
    body : CExpr
