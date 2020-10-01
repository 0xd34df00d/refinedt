{-# OPTIONS --safe #-}

module Surface.Syntax where

open import Agda.Builtin.Bool
open import Agda.Builtin.List public

open import Data.Nat.Base public hiding (compare)
open import Data.Fin
open import Data.Product public using (_×_)
open import Data.Product using (_,_)
open import Data.Vec

open import Common.NamingContext

data BaseType : Set where
  BUnit : BaseType

Ctx : ℕ → Set
data SType (Γ↓ : NamingCtx) : Set
data STerm (Γ↓ : NamingCtx) : Set
data Refinement (Γ↓ : NamingCtx) : Set
CaseBranches : ℕ → NamingCtx → Set
ADTCons : ℕ → NamingCtx → Set
Ctx n = Vec (SType (MkNamingCtx n)) n

data STerm Γ↓ where
  SVar  : (var : Var Γ↓) → STerm Γ↓
  SLam  : (τ : SType Γ↓) → (ε : STerm (expand-Γ↓ Γ↓)) → STerm Γ↓
  SApp  : (ε₁ : STerm Γ↓) → (ε₂ : STerm Γ↓) → STerm Γ↓
  SUnit : STerm Γ↓
  SCase : {bn : _} → (scrut : STerm Γ↓) → (branches : CaseBranches bn Γ↓) → STerm Γ↓
  SCon  : {bn : _} → (idx : Fin bn) → (body : STerm Γ↓) → (adtCons : ADTCons bn Γ↓) → STerm Γ↓

data SType Γ↓ where
  SRBT : (b : BaseType) → (ρ : Refinement (expand-Γ↓ Γ↓)) → SType Γ↓
  SArr : (τ₁ : SType Γ↓) → (τ₂ : SType (expand-Γ↓ Γ↓)) → SType Γ↓
  SADT : {n : _} → (cons : ADTCons (suc n) Γ↓) → SType Γ↓

data Refinement Γ↓ where
  _≈_ : STerm Γ↓ → STerm Γ↓ → Refinement Γ↓
  _∧_ : (ρ₁ : Refinement Γ↓) → (ρ₂ : Refinement Γ↓) → Refinement Γ↓

record CaseBranch (Γ↓ : NamingCtx) : Set where
  constructor MkCaseBranch
  inductive
  field
    body : STerm (expand-Γ↓ Γ↓)

CaseBranches n Γ↓ = Vec (CaseBranch Γ↓) n

ADTCons n Γ↓ = Vec (SType Γ↓) n

infix 15 _∣_
_∣_ : (b : BaseType) → (ρ : Refinement (expand-Γ↓ Γ↓)) → SType Γ↓
_∣_ = SRBT

Τ : Refinement Γ↓
Τ = SUnit ≈ SUnit

variable
  Γ Γ' Δ : Ctx n
  τ τ' τ₁ τ₂ τ₁' τ₂' τᵢ τⱼ σ : SType Γ↓
  ε ε' ε₁ ε₂ ε₁' ε₂' ϖ : STerm Γ↓
  b b' b₁ b₂ : BaseType
  ρ ρ₁ ρ₂ : Refinement Γ↓

open NamingCtx

record Cutoff (Γ↓ : NamingCtx) : Set where
  constructor MkCutoff
  field
    cutoff : Fin (suc (ctx-len Γ↓))

open Cutoff

zero-cutoff : Cutoff Γ↓
zero-cutoff = MkCutoff zero

inc-cutoff : Cutoff Γ↓ → Cutoff (expand-Γ↓ Γ↓)
inc-cutoff (MkCutoff c) = MkCutoff (suc c)

ShiftType : (NamingCtx → Set) → Set
ShiftType ty = ∀ {Γ↓} → Cutoff Γ↓ → ty Γ↓ → ty (expand-Γ↓ Γ↓)

shift-ε'    : ShiftType STerm
shift-τ'    : ShiftType SType
shift-ρ'    : ShiftType Refinement
shift-b'    : ShiftType CaseBranch
shift-bs'   : ShiftType (CaseBranches n)
shift-cons' : ShiftType (ADTCons n)

shift-ε' c (SVar var) with raise 1 var
... | var↑ with compare var↑ (cutoff c)
... | less _ _ = SVar var↑
... | _ = SVar (suc var)
shift-ε' c (SLam τ ε) = SLam (shift-τ' c τ) (shift-ε' (inc-cutoff c) ε)
shift-ε' c (SApp ε₁ ε₂) = SApp (shift-ε' c ε₁) (shift-ε' c ε₂)
shift-ε' c SUnit = SUnit
shift-ε' c (SCase ε branches) = SCase (shift-ε' c ε) (shift-bs' c branches)
shift-ε' c (SCon idx ε adtCons) = SCon idx (shift-ε' c ε) (shift-cons' c adtCons)

shift-b' c (MkCaseBranch body) = MkCaseBranch (shift-ε' (inc-cutoff c) body)

shift-bs' c [] = []
shift-bs' c (b ∷ bs) = shift-b' c b ∷ shift-bs' c bs

shift-cons' c [] = []
shift-cons' c (τ ∷ cons) = shift-τ' c τ ∷ shift-cons' c cons

shift-τ' c (SRBT b ρ) = SRBT b (shift-ρ' (inc-cutoff c) ρ)
shift-τ' c (SArr τ₁ τ₂) = SArr (shift-τ' c τ₁) (shift-τ' (inc-cutoff c) τ₂)
shift-τ' c (SADT cons) = SADT (shift-cons' c cons)

shift-ρ' c (ε₁ ≈ ε₂) = shift-ε' c ε₁ ≈ shift-ε' c ε₂
shift-ρ' c (ρ₁ ∧ ρ₂) = shift-ρ' c ρ₁ ∧ shift-ρ' c ρ₂

shift-ε : STerm Γ↓ → STerm (expand-Γ↓ Γ↓)
shift-ε = shift-ε' zero-cutoff

shift-τ : SType Γ↓ → SType (expand-Γ↓ Γ↓)
shift-τ = shift-τ' zero-cutoff

shift-ρ : Refinement Γ↓ → Refinement (expand-Γ↓ Γ↓)
shift-ρ = shift-ρ' zero-cutoff
