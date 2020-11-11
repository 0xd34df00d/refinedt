module Surface.WellScoped where

open import Agda.Builtin.Bool
open import Agda.Builtin.List public
open import Agda.Builtin.String

open import Data.Nat.Base public
open import Data.Fin public using (Fin)
open import Data.Vec

data BaseType : Set where
  BUnit : BaseType

variable
  n ℓ : ℕ
  b b' b₁ b₂ : BaseType

data SType (ℓ : ℕ) : Set
data STerm (ℓ : ℕ) : Set
data Refinement (ℓ : ℕ) : Set

data SType ℓ where
  ⟨_∣_⟩ : (b : BaseType)
        → (ρ : Refinement (suc ℓ))
        → SType ℓ
  _⇒_   : (τ₁ : SType ℓ)
        → (τ₂ : SType (suc ℓ))
        → SType ℓ
  -- TODO adts

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

module WeakenScope where
  ws-ε : STerm ℓ → STerm (suc ℓ)
  ws-ρ : Refinement ℓ → Refinement (suc ℓ)
  ws-τ : SType ℓ → SType (suc ℓ)

  ws-ε SUnit = SUnit
  ws-ε (SVar idx) = SVar {! !}
  ws-ε (SLam τ ε) = SLam (ws-τ τ) (ws-ε ε)
  ws-ε (SApp ε₁ ε₂) = SApp (ws-ε ε₁) (ws-ε ε₂)

  ws-ρ (ε₁ ≃ ε₂) = ws-ε ε₁ ≃ ws-ε ε₂
  ws-ρ (ρ₁ ∧ ρ₂) = ws-ρ ρ₁ ∧ ws-ρ ρ₂

  ws-τ ⟨ b ∣ ρ ⟩ = ⟨ b ∣ ws-ρ ρ ⟩
  ws-τ (τ₁ ⇒ τ₂) = ws-τ τ₁ ⇒ ws-τ τ₂
Τ : Refinement ℓ
Τ = SUnit ≃ SUnit

variable
  Γ Γ' Δ : Ctx ℓ
