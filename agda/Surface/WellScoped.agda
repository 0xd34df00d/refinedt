{-# OPTIONS --safe #-}

module Surface.WellScoped where

open import Data.Fin public using (Fin)
open import Data.Nat public using (ℕ; suc)
open import Data.Vec
open import Relation.Binary.PropositionalEquality using (_≡_)

data BaseType : Set where
  BUnit : BaseType

record ℕₐ : Set where
  constructor Mkℕₐ
  field
    get-length : ℕ

variable
  n ℓ ℓ' ℓ₀ ℓ₁ ℓ₂ : ℕ
  nₐ : ℕₐ
  b b' b₁ b₂ : BaseType
  idx ι ι₁ ι₂ : Fin ℓ

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

-- NOTE having `SType ℓ` instead of `SType (suc ℓ)` in SLam's type prevents the type from referring the argument itself,
-- which kinda breaks T-Exact and similar rules from the refinement reflection paper,
-- but now I'm not sure if agreement holds for the type system in that paper.
data STerm ℓ where
  SUnit : STerm ℓ
  SVar  : (idx : Fin ℓ)
        → STerm ℓ
  SLam  : (τ : SType ℓ)
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
  _≈_ : (ε₁ ε₂ : STerm ℓ) → Refinement ℓ
  _∧_ : (ρ₁ ρ₂ : Refinement ℓ) → Refinement ℓ


infixl 5 _,_
data Ctx : ℕ → Set where
  ⊘   : Ctx 0
  _,_ : Ctx ℓ → SType ℓ → Ctx (suc ℓ)

variable
  Γ Γ' Δ : Ctx ℓ
  τ τ' τ₀ τ₀' τ₁ τ₂ τ₁' τ₂' τᵢ τⱼ σ : SType ℓ
  ε ε' ε₀ ε₁ ε₁' ε₂ ε₂' ϖ : STerm ℓ
  ρ₁ ρ₂ ρ₃ : Refinement ℓ

Τ : Refinement ℓ
Τ = SUnit ≈ SUnit

record VarAction : Set₁ where
  field
    Target : ℕ → Set
    var-action : (Fin ℓ → Target ℓ')
               → (Fin ℓ → STerm ℓ')
    ext : (Fin ℓ → Target ℓ')
        → (Fin (suc ℓ) → Target (suc ℓ'))

record VarActionProps (act : VarAction) : Set where
  open VarAction act
  field
    ≡-ext : {f₁ f₂ : Fin ℓ → Target ℓ'}
          → (∀ x → f₁ x ≡ f₂ x)
          → (∀ x → ext f₁ x ≡ ext f₂ x)
    var-action-cong : {f₁ f₂ : Fin ℓ → Target ℓ'}
                    → (∀ x → f₁ x ≡ f₂ x)
                    → (∀ x → var-action f₁ x ≡ var-action f₂ x)
