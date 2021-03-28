{-# OPTIONS --safe #-}

module Core.Syntax where

open import Data.Fin public using (Fin)
open import Data.Nat public using (ℕ; suc; _+_)
open import Data.Vec using (Vec)

open import Common.Types public

variable
  k n ℓ ℓ' ℓ₀ ℓ₁ ℓ₂ : ℕ
  idx ι ι₁ ι₂ : Fin ℓ

data Sort : Set where
  ⋆ : Sort
  □ : Sort

data CExpr (ℓ : ℕ) : Set

ADTCons : ℕₐ → ℕ → Set
ADTCons (Mkℕₐ n) ℓ = Vec (CExpr ℓ) n

CaseBranches : ℕₐ → ℕ → Set
CaseBranches (Mkℕₐ n) ℓ = Vec (CExpr (2 + ℓ)) n
-- ^ By convention, the variable 0 is the scrutinee and the variable 1 is the proof of η-equality

data CExpr ℓ where
  CVar  : (ι : Fin ℓ)
        → CExpr ℓ
  CSort : (s : Sort)
        → CExpr ℓ
  CΠ    : (τ₁ : CExpr ℓ)
        → (τ₂ : CExpr (suc ℓ))
        → CExpr ℓ
  CLam  : (τ : CExpr ℓ)
        → (ε : CExpr (suc ℓ))
        → CExpr ℓ
  CApp  : (ε₁ ε₂ : CExpr ℓ)
        → CExpr ℓ
  Cunit : CExpr ℓ
  CUnit : CExpr ℓ
  CADT  : (cons : ADTCons (Mkℕₐ (suc n)) ℓ)
        → CExpr ℓ
  CCon  : (ι : Fin n)
        → (ε : CExpr ℓ)
        → (cons : ADTCons (Mkℕₐ n) ℓ)
        → CExpr ℓ
  CCase : (scrut : CExpr ℓ)
        → (branches : CaseBranches nₐ ℓ)
        → CExpr ℓ

⋆ₑ : CExpr ℓ
⋆ₑ = CSort ⋆

□ₑ : CExpr ℓ
□ₑ = CSort □

infixl 5 _·_
_·_ : CExpr ℓ → CExpr ℓ → CExpr ℓ
_·_ = CApp

infixl 5 _,_
data Ctx : ℕ → Set where
  ⊘   : Ctx 0
  _,_ : Ctx ℓ → CExpr ℓ → Ctx (suc ℓ)

variable
  τ τ' τ₁ τ₂ τ₁' τ₂' τᵢ τⱼ σ : CExpr ℓ
  ε ε' ε₁ ε₂ ε₃ ε₁' ε₂' ϖ : CExpr ℓ
  s s₁ s₂ : Sort
  Γ Γ' : Ctx ℓ

record VarAction : Set₁ where
  field
    Target : ℕ → Set
    var-action : Target ℓ → CExpr ℓ
    ext : (Fin ℓ → Target ℓ')
        → (Fin (suc ℓ) → Target (suc ℓ'))
