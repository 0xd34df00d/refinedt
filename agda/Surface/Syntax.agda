{-# OPTIONS --safe #-}

module Surface.Syntax where

open import Data.Fin public using (Fin)
open import Data.Nat public using (ℕ; suc)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Common.Types public

data BaseType : Set where
  BUnit : BaseType

variable
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
  ⊍_    : (cons : ADTCons (Mkℕₐ n) ℓ)
        → SType ℓ

-- NOTE having `SType ℓ` instead of `SType (suc ℓ)` in SLam's type
-- prevents the type from referring the argument itself,
-- which kinda breaks T-Exact and similar rules from the refinement reflection paper,
-- but now I'm not sure if agreement holds for the type system in that paper.
data STerm ℓ where
  SUnit : STerm ℓ
  SVar  : (ι : Fin ℓ)
        → STerm ℓ
  SLam  : (τ : SType ℓ)
        → (ε : STerm (suc ℓ))
        → STerm ℓ
  SApp  : (ε₁ ε₂ : STerm ℓ)
        → STerm ℓ
  SCase : (ε : STerm ℓ)
        → (cons : ADTCons nₐ ℓ)
        → (τ : SType ℓ)
        → (branches : CaseBranches nₐ ℓ)
        → STerm ℓ
  SCon  : (ι : Fin n)
        → (body : STerm ℓ)
        → (cons : ADTCons (Mkℕₐ n) ℓ)
        → STerm ℓ

data Refinement ℓ where
  _≈_of_ : (ε₁ ε₂ : STerm ℓ) → (τ : SType ℓ) → Refinement ℓ
  _∧_    : (ρ₁ ρ₂ : Refinement ℓ) → Refinement ℓ
  Τ      : Refinement ℓ


infixl 5 _,_
data Ctx : ℕ → Set where
  ⊘   : Ctx 0
  _,_ : Ctx ℓ → SType ℓ → Ctx (suc ℓ)

variable
  Γ Γ' : Ctx ℓ
  τ τ' τ₀ τ₀' τ₁ τ₂ τ₁' τ₂' τ₃ τ₃' τᵢ τⱼ σ σ' : SType ℓ
  ε ε' ε₀ ε₁ ε₁' ε₂ ε₂' ε₃ ε₃' ϖ σε : STerm ℓ
  ρ ρ₁ ρ₂ ρ₃ : Refinement ℓ

record VarAction : Set₁ where
  field
    Target : ℕ → Set
    var-action : Target ℓ → STerm ℓ
    ext : (Fin ℓ → Target ℓ')
        → (Fin (suc ℓ) → Target (suc ℓ'))

record VarActionProps (act : VarAction) : Set where
  open VarAction act
  field
    ≡-ext : {f₁ f₂ : Fin ℓ → Target ℓ'}
          → (∀ x → f₁ x ≡ f₂ x)
          → (∀ x → ext f₁ x ≡ ext f₂ x)
    ext-id : ∀ {f : Fin ℓ → Target ℓ}
           → (∀ x → var-action (f x) ≡ SVar x)
           → (∀ x → var-action (ext f x) ≡ SVar x)
