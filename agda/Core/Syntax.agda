module Core.Syntax where

open import Agda.Builtin.List public
open import Agda.Builtin.String
open import Data.Nat.Base public
open import Data.Fin public using (Fin)
open import Data.Product public using (_×_)
open import Data.Product using (_,_)
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
  CSort : (s : Sort) → CExpr
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

CtxElem : Set
CtxElem = Var × CExpr

Ctx : Set
Ctx = List CtxElem

infixl 21 _,_⦂_
_,_⦂_ : Ctx → Var → CExpr → Ctx
Γ , x ⦂ τ = ( x , τ ) ∷ Γ

infix 19 _⦂_
_⦂_ : Var → CExpr → Var × CExpr
_⦂_ = _,_

variable
  Γ Γ' Δ : Ctx
  x x' x₁ x₂ y ν ν₁ ν₂ : Var
  τ τ' τ₁ τ₂ τ₁' τ₂' τᵢ τⱼ σ : CExpr
  ε ε' ε₁ ε₂ ε₁' ε₂' : CExpr
  b b' b₁ b₂ : CExpr
  n : ℕ
  s : Sort
