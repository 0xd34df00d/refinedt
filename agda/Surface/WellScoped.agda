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
  b b' b₁ b₂ : BaseType

data SType (ℓ : ℕ) : Set
data STerm (ℓ : ℕ) : Set
data Refinement (ℓ : ℕ) : Set

ADTCons : ℕₐ → ℕ → Set
ADTCons (Mkℕₐ n) ℓ = Vec (SType ℓ) n

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
  -- TODO SCase and SCon

data Refinement ℓ where
  _≃_ : (ε₁ ε₂ : STerm ℓ) → Refinement ℓ
  _∧_ : (ρ₁ ρ₂ : Refinement ℓ) → Refinement ℓ


infixl 5 _,_
data Ctx : ℕ → Set where
  ⊘   : Ctx 0
  _,_ : Ctx ℓ → SType ℓ → Ctx (suc ℓ)

module RenameScope where
  ext : (Fin ℓ → Fin ℓ')
      → Fin (suc ℓ) → Fin (suc ℓ')
  ext f zero = zero
  ext f (suc n) = suc (f n)

  Renamer : (ℕ → Set) → Set
  Renamer Ty = ∀ {ℓ ℓ'} → (Fin ℓ → Fin ℓ') → Ty ℓ → Ty ℓ'

  rename-ρ : Renamer Refinement
  rename-τ : Renamer SType
  rename-ε : Renamer STerm

  rename-ρ f (ε₁ ≃ ε₂) = rename-ε f ε₁ ≃ rename-ε f ε₂
  rename-ρ f (ρ₁ ∧ ρ₂) = rename-ρ f ρ₁ ∧ rename-ρ f ρ₂

  rename-τ f ⟨ b ∣ ρ ⟩ = ⟨ b ∣ rename-ρ (ext f) ρ ⟩
  rename-τ f (τ₁ ⇒ τ₂) = rename-τ f τ₁ ⇒ rename-τ (ext f) τ₂
  rename-τ {ℓ} {ℓ'}
           f (⊍ cons)  = ⊍ (go cons)
    where
      go : ∀ {n} → ADTCons n ℓ → ADTCons n ℓ'
      go [] = []
      go (τ ∷ τs) = rename-τ f τ ∷ go τs

  rename-ε f SUnit = SUnit
  rename-ε f (SVar idx) = SVar (f idx)
  rename-ε f (SLam τ ε) = SLam (rename-τ (ext f) τ) (rename-ε (ext f) ε)
  rename-ε f (SApp ε₁ ε₂) = SApp (rename-ε f ε₁) (rename-ε f ε₂)

  ws-τ : SType ℓ → SType (suc ℓ)
  ws-τ = rename-τ suc

variable
  Γ Γ' Δ : Ctx ℓ
  τ τ' τ₁ τ₂ : SType ℓ

infix 4 _∈_
data _∈_ : SType ℓ → Ctx ℓ → Set where
  ∈-zero : RenameScope.ws-τ τ ∈ Γ , τ
  ∈-suc  : τ ∈ Γ
         → RenameScope.ws-τ τ ∈ Γ , τ'


Τ : Refinement ℓ
Τ = SUnit ≃ SUnit
