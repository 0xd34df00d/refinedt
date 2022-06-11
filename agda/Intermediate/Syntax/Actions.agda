{-# OPTIONS --safe #-}

open import Intermediate.Syntax

module Intermediate.Syntax.Actions (α : VarAction) where

open import Data.Nat using (zero; suc; _+_)
open import Data.Vec

open VarAction α public

var-action-record : VarAction
var-action-record = α

ActionOn : (ℕ → Set) → Set
ActionOn Ty = ∀ {ℓ ℓ'} → (Fin ℓ → Target ℓ') → Ty ℓ → Ty ℓ'

mutual
  act-ρ : ActionOn IRefinement
  act-ρ f (ε₁ ≈ ε₂ of τ) = act-ε f ε₁ ≈ act-ε f ε₂ of act-τ f τ
  act-ρ f (ρ₁ ∧ ρ₂) = act-ρ f ρ₁ ∧ act-ρ f ρ₂
  act-ρ f Τ = Τ

  act-τ : ActionOn IType
  act-τ f ⟨ b ∣ ρ ⟩ = ⟨ b ∣ act-ρ (ext f) ρ ⟩
  act-τ f (τ₁ ⇒ τ₂) = act-τ f τ₁ ⇒ act-τ (ext f) τ₂
  act-τ f (⊍ cons)  = ⊍ (act-cons f cons)

  act-cons : ActionOn (ADTCons nₐ)
  act-cons _ [] = []
  act-cons f (τ ∷ τs) = act-τ f τ ∷ act-cons f τs

  act-branches : ActionOn (CaseBranches nₐ)
  act-branches _ [] = []
  act-branches f (MkCaseBranch body ∷ bs) = MkCaseBranch (act-ε (ext f) body) ∷ act-branches f bs

  act-ε : ActionOn ITerm
  act-ε f IUnit = IUnit
  act-ε f (IVar ι) = var-action (f ι)
  act-ε f (ILam τ ε) = ILam (act-τ f τ) (act-ε (ext f) ε)
  act-ε f (IApp ε₁ ε₂) = IApp (act-ε f ε₁) (act-ε f ε₂)
  act-ε f (ICase scrut branches) = ICase (act-ε f scrut) (act-branches f branches)
  act-ε f (ICon ι body adt-cons) = ICon ι (act-ε f body) (act-cons f adt-cons)
  act-ε f (ε I<: τ) = act-ε f ε I<: act-τ f τ


ext-k : ∀ k
      → (Fin ℓ → Target ℓ')
      → (Fin (k + ℓ) → Target (k + ℓ'))
ext-k zero ρ = ρ
ext-k (suc k) ρ = ext (ext-k k ρ)
