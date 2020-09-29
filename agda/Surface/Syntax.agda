{-# OPTIONS --safe #-}

module Surface.Syntax where

open import Agda.Builtin.Bool
open import Agda.Builtin.List public

open import Data.Nat.Base public
open import Data.Fin public using (Fin)
open import Data.Product public using (_×_)
open import Data.Product using (_,_)
open import Data.Vec

variable
  n : ℕ

data BaseType : Set where
  BUnit : BaseType


data Ctx : ℕ → Set
data SType (Γ : Ctx n) : Set
data STerm (Γ : Ctx n) : Set
data Refinement (Γ : Ctx n) : Set
CaseBranches : Ctx n → ℕ → Set
ADTCons : Ctx n → ℕ → Set
Τ : ∀ {Γ} → Refinement Γ

data Ctx where
  empty : Ctx 0
  _,_ : {n : ℕ} → (Γ : Ctx n) → (τ : SType Γ) → Ctx (suc n)

record CaseBranch {n} (Γ : Ctx n) : Set

data STerm {n} Γ where
  SVar  : (var : Fin n) → STerm Γ
  SLam  : (τ : SType Γ) → (ε : STerm (Γ , τ)) → STerm Γ
  SApp  : (ε₁ : STerm Γ) → (ε₂ : STerm Γ) → STerm Γ
  SUnit : STerm Γ
  SCase : {bn : _} → (scrut : STerm Γ) → (branches : CaseBranches Γ bn) → STerm Γ
  SCon  : {bn : _} → (idx : Fin bn) → (body : STerm Γ) → (adtCons : ADTCons Γ bn) → STerm Γ

data SType Γ where
  SRBT : (b : BaseType) → (ρ : Refinement (Γ , SRBT b Τ)) → SType Γ
  SArr : (τ₁ : SType Γ) → (τ₂ : SType (Γ , τ₁)) → SType Γ
  SADT : {n : _} → (cons : ADTCons Γ (suc n)) → SType Γ

data Refinement Γ where
  _≈_ : STerm Γ → STerm Γ → Refinement Γ
  _∧_ : (ρ₁ : Refinement Γ) → (ρ₂ : Refinement Γ) → Refinement Γ

record CaseBranch Γ where
  constructor MkCaseBranch
  inductive
  field
    τ : SType Γ
    body : STerm (Γ , τ)

CaseBranches Γ n = Vec (CaseBranch Γ) n

ADTCons Γ n = Vec (SType Γ) n

{-
infix 15 _∣_
_∈_∣_ : (b : BaseType) → (ρ : Refinement) → SType
_∈_∣_ = SRBT
-}

Τ = SUnit ≈ SUnit

variable
  Γ Γ' Δ : Ctx n
  τ τ' τ₁ τ₂ τ₁' τ₂' τᵢ τⱼ σ : SType Γ
  ε ε' ε₁ ε₂ ε₁' ε₂' ϖ : STerm Γ
  b b' b₁ b₂ : BaseType
  ρ ρ₁ ρ₂ : Refinement Γ
