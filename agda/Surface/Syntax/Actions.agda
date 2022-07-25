{-# OPTIONS --safe #-}

open import Surface.Syntax

module Surface.Syntax.Actions (α : VarAction) where

open import Data.Nat using (zero; suc; _+_)
open import Data.Vec

open VarAction α public

var-action-record : VarAction
var-action-record = α

ActionOn : (ℕ → Set) → Set
ActionOn Ty = ∀ {ℓ ℓ'} → (Fin ℓ → Target ℓ') → Ty ℓ → Ty ℓ'

mutual
  act-ρ : ActionOn Refinement
  act-ρ f (ε₁ ≈ ε₂ of τ) = act-ε f ε₁ ≈ act-ε f ε₂ of act-τ f τ
  act-ρ f (ρ₁ ∧ ρ₂) = act-ρ f ρ₁ ∧ act-ρ f ρ₂
  act-ρ f Τ = Τ

  act-τ : ActionOn SType
  act-τ f ⟨ b ∣ ρ ⟩ = ⟨ b ∣ act-ρ (ext f) ρ ⟩
  act-τ f (τ₁ ⇒ τ₂) = act-τ f τ₁ ⇒ act-τ (ext f) τ₂
  act-τ f (⊍ cons)  = ⊍ (act-cons f cons)

  act-cons : ActionOn (ADTCons nₐ)
  act-cons _ [] = []
  act-cons f (τ ∷ τs) = act-τ f τ ∷ act-cons f τs

  act-branches : ActionOn (CaseBranches nₐ)
  act-branches _ [] = []
  act-branches f (MkCaseBranch body ∷ bs) = MkCaseBranch (act-ε (ext f) body) ∷ act-branches f bs

  act-ε : ActionOn STerm
  act-ε f SUnit = SUnit
  act-ε f (SVar ι) = var-action (f ι)
  act-ε f (SLam τ ε) = SLam (act-τ f τ) (act-ε (ext f) ε)
  act-ε f (SApp ε₁ ε₂) = SApp (act-ε f ε₁) (act-ε f ε₂)
  act-ε f (SCase ε cons τ branches) = SCase (act-ε f ε) (act-cons f cons) (act-τ f τ) (act-branches f branches)
  act-ε f (SCon ι body cons) = SCon ι (act-ε f body) (act-cons f cons)


ext-k : ∀ k
      → (Fin ℓ → Target ℓ')
      → (Fin (k + ℓ) → Target (k + ℓ'))
ext-k zero ρ = ρ
ext-k (suc k) ρ = ext (ext-k k ρ)
