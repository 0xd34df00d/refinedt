{-# OPTIONS --safe #-}

module Surface.WellScoped where

open import Agda.Builtin.Bool
open import Agda.Builtin.List public
open import Agda.Builtin.String

open import Data.Nat.Base public
open import Data.Fin public using (Fin; suc; zero)
open import Data.Vec

data BaseType : Set where
  BUnit : BaseType

record ℕₐ : Set where
  constructor Mkℕₐ
  field
    get-length : ℕ

variable
  n ℓ ℓ' : ℕ
  nₐ : ℕₐ
  b b' b₁ b₂ : BaseType

data SType (ℓ : ℕ) : Set
data STerm (ℓ : ℕ) : Set
data Refinement (ℓ : ℕ) : Set

ADTCons : ℕₐ → ℕ → Set
ADTCons (Mkℕₐ n) ℓ = Vec (SType ℓ) n

record CaseBranch (ℓ : ℕ) : Set where
  constructor MkCaseBranch
  inductive
  field
    body : STerm (suc ℓ)

CaseBranches : ℕₐ → ℕ → Set
CaseBranches (Mkℕₐ n) ℓ = Vec (CaseBranch ℓ) n

data SType ℓ where
  ⟨_∣_⟩ : (b : BaseType)
        → (ρ : Refinement (suc ℓ))
        → SType ℓ
  _⇒_   : (τ₁ : SType ℓ)
        → (τ₂ : SType (suc ℓ))
        → SType ℓ
  ⊍_    : (cons : ADTCons (Mkℕₐ (suc n)) ℓ)
        → SType ℓ

data STerm ℓ where
  SUnit : STerm ℓ
  SVar  : (idx : Fin ℓ)
        → STerm ℓ
  SLam  : (τ : SType (suc ℓ))
        → (ε : STerm (suc ℓ))
        → STerm ℓ
  SApp  : (ε₁ ε₂ : STerm ℓ)
        → STerm ℓ
  SCase : (scrut : STerm ℓ)
        → (branches : CaseBranches nₐ ℓ)
        → STerm ℓ
  SCon  : (idx : Fin n)
        → (body : STerm ℓ)
        → (adt-cons : ADTCons (Mkℕₐ n) ℓ)
        → STerm ℓ

data Refinement ℓ where
  _≃_ : (ε₁ ε₂ : STerm ℓ) → Refinement ℓ
  _∧_ : (ρ₁ ρ₂ : Refinement ℓ) → Refinement ℓ


infixl 5 _,_
data Ctx : ℕ → Set where
  ⊘   : Ctx 0
  _,_ : Ctx ℓ → SType ℓ → Ctx (suc ℓ)

variable
  Γ Γ' Δ : Ctx ℓ
  τ τ' τ₁ τ₂ : SType ℓ

Τ : Refinement ℓ
Τ = SUnit ≃ SUnit


module RenameScoped where
  ext : (Fin ℓ → Fin ℓ')
      → Fin (suc ℓ) → Fin (suc ℓ')
  ext r zero = zero
  ext r (suc n) = suc (r n)

  Renamer : (ℕ → Set) → Set
  Renamer Ty = ∀ {ℓ ℓ'} → (Fin ℓ → Fin ℓ') → Ty ℓ → Ty ℓ'

  rename-ρ : Renamer Refinement
  rename-τ : Renamer SType
  rename-ε : Renamer STerm
  rename-cons : Renamer (ADTCons nₐ)

  rename-ρ r (ε₁ ≃ ε₂) = rename-ε r ε₁ ≃ rename-ε r ε₂
  rename-ρ r (ρ₁ ∧ ρ₂) = rename-ρ r ρ₁ ∧ rename-ρ r ρ₂

  rename-τ r ⟨ b ∣ ρ ⟩ = ⟨ b ∣ rename-ρ (ext r) ρ ⟩
  rename-τ r (τ₁ ⇒ τ₂) = rename-τ r τ₁ ⇒ rename-τ (ext r) τ₂
  rename-τ r (⊍ cons)  = ⊍ (rename-cons r cons)

  rename-cons _ [] = []
  rename-cons r (τ ∷ τs) = rename-τ r τ ∷ rename-cons r τs

  rename-ε r SUnit = SUnit
  rename-ε r (SVar idx) = SVar (r idx)
  rename-ε r (SLam τ ε) = SLam (rename-τ (ext r) τ) (rename-ε (ext r) ε)
  rename-ε r (SApp ε₁ ε₂) = SApp (rename-ε r ε₁) (rename-ε r ε₂)
  rename-ε r (SCase scrut branches) = SCase (rename-ε r scrut) (go r branches)
    where
      go : ∀ {n} → (Fin ℓ → Fin ℓ') → CaseBranches n ℓ → CaseBranches n ℓ'
      go _ [] = []
      go r (MkCaseBranch body ∷ bs) = MkCaseBranch (rename-ε (ext r) body) ∷ go r bs
  rename-ε r (SCon idx body adt-cons) = SCon idx (rename-ε r body) (rename-cons r adt-cons)

  weaken-τ : SType ℓ → SType (suc ℓ)
  weaken-τ = rename-τ suc

  weaken-ε : STerm ℓ → STerm (suc ℓ)
  weaken-ε = rename-ε suc

module SubstScoped where
  exts : (Fin ℓ → STerm ℓ')
       → (Fin (suc ℓ) → STerm (suc ℓ'))
  exts σ zero = SVar zero
  exts σ (suc n) = RenameScoped.weaken-ε (σ n)

  Subster : (ℕ → Set) → Set
  Subster Ty = ∀ {ℓ ℓ'} → (Fin ℓ → STerm ℓ') → Ty ℓ → Ty ℓ'

  subst-ρ : Subster Refinement
  subst-τ : Subster SType
  subst-ε : Subster STerm
  subst-cons : Subster (ADTCons nₐ)

  subst-ρ σ (ε₁ ≃ ε₂) = subst-ε σ ε₁ ≃ subst-ε σ ε₂
  subst-ρ σ (ρ₁ ∧ ρ₂) = subst-ρ σ ρ₁ ∧ subst-ρ σ ρ₂

  subst-τ σ ⟨ b ∣ ρ ⟩ = ⟨ b ∣ subst-ρ (exts σ) ρ ⟩
  subst-τ σ (τ₁ ⇒ τ₂) = subst-τ σ τ₁ ⇒ subst-τ (exts σ) τ₂
  subst-τ σ (⊍ cons) = ⊍ (subst-cons σ cons)

  subst-cons _ [] = []
  subst-cons σ (τ ∷ τs) = subst-τ σ τ ∷ subst-cons σ τs

  subst-ε σ SUnit = SUnit
  subst-ε σ (SVar idx) = σ idx
  subst-ε σ (SLam τ ε) = SLam (subst-τ (exts σ) τ) (subst-ε (exts σ) ε)
  subst-ε σ (SApp ε₁ ε₂) = SApp (subst-ε σ ε₁) (subst-ε σ ε₂)
  subst-ε σ (SCase ε branches) = SCase (subst-ε σ ε) {! !}
  subst-ε σ (SCon idx ε cons) = SCon idx (subst-ε σ ε) (subst-cons σ cons)

infix 4 _∈_
data _∈_ : SType ℓ → Ctx ℓ → Set where
  ∈-zero : RenameScoped.weaken-τ τ ∈ Γ , τ
  ∈-suc  : τ ∈ Γ
         → RenameScoped.weaken-τ τ ∈ Γ , τ'

