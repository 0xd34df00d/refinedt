{-# OPTIONS --safe #-}

open import Surface.WellScoped

module Surface.WellScoped.ActionsLemmas (act : VarAction) (props : VarActionProps act) where

open import Data.Vec
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.WellScoped.Actions act
open VarActionProps props

ActExtensionality : {Ty : ℕ → Set} → ActionOn Ty → Set
ActExtensionality {Ty} act = ∀ {ℓ ℓ'}
                             → {f₁ f₂ : Fin ℓ → Target ℓ'}
                             → ((x : Fin ℓ) → f₁ x ≡ f₂ x)
                             → (v : Ty ℓ)
                             → act f₁ v ≡ act f₂ v

act-τ-extensionality : ActExtensionality act-τ
act-ρ-extensionality : ActExtensionality act-ρ
act-ε-extensionality : ActExtensionality act-ε
act-cons-extensionality : ActExtensionality {ADTCons nₐ} act-cons
act-branches-extensionality : ActExtensionality {CaseBranches nₐ} act-branches

act-τ-extensionality x-≡ ⟨ b ∣ ρ ⟩ rewrite act-ρ-extensionality (≡-ext x-≡) ρ = refl
act-τ-extensionality x-≡ (τ₁ ⇒ τ₂) rewrite act-τ-extensionality x-≡ τ₁
                                         | act-τ-extensionality (≡-ext x-≡) τ₂ = refl
act-τ-extensionality x-≡ (⊍ cons) rewrite act-cons-extensionality x-≡ cons = refl

act-ρ-extensionality x-≡ (ε₁ ≈ ε₂) rewrite act-ε-extensionality x-≡ ε₁
                                         | act-ε-extensionality x-≡ ε₂ = refl
act-ρ-extensionality x-≡ (ρ₁ ∧ ρ₂) rewrite act-ρ-extensionality x-≡ ρ₁
                                         | act-ρ-extensionality x-≡ ρ₂ = refl

act-ε-extensionality x-≡ SUnit = refl
act-ε-extensionality x-≡ (SVar idx) rewrite var-action-cong x-≡ idx = refl
act-ε-extensionality x-≡ (SLam τ ε) rewrite act-τ-extensionality x-≡ τ
                                          | act-ε-extensionality (≡-ext x-≡) ε = refl
act-ε-extensionality x-≡ (SApp ε₁ ε₂) rewrite act-ε-extensionality x-≡ ε₁
                                            | act-ε-extensionality x-≡ ε₂ = refl
act-ε-extensionality x-≡ (SCase ε branches) rewrite act-ε-extensionality x-≡ ε
                                                  | act-branches-extensionality x-≡ branches = refl
act-ε-extensionality x-≡ (SCon idx ε cons) rewrite act-ε-extensionality x-≡ ε
                                                 | act-cons-extensionality x-≡ cons = refl

act-cons-extensionality x-≡ [] = refl
act-cons-extensionality x-≡ (τ ∷ τs) rewrite act-τ-extensionality x-≡ τ
                                           | act-cons-extensionality x-≡ τs = refl

act-branches-extensionality x-≡ [] = refl
act-branches-extensionality x-≡ (MkCaseBranch body ∷ bs) rewrite act-ε-extensionality (≡-ext x-≡) body
                                                               | act-branches-extensionality x-≡ bs = refl
