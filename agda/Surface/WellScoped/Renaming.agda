{-# OPTIONS --safe #-}

module Surface.WellScoped.Renaming where

open import Data.Fin using (zero; suc)
open import Data.Nat using (_+_; zero; suc)
open import Data.Vec
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import Surface.WellScoped
open import Surface.WellScoped.Actions (record { Target = Fin
                                               ; var-action = λ r idx → SVar (r idx)
                                               ; ext = λ where _ zero → zero
                                                               r (suc n) → suc (r n)
                                               }) public

weaken-τ : SType ℓ → SType (suc ℓ)
weaken-τ = act-τ suc

weaken-ε : STerm ℓ → STerm (suc ℓ)
weaken-ε = act-ε suc

weaken-τ-k : ∀ k → SType ℓ → SType (k + ℓ)
weaken-τ-k zero τ = τ
weaken-τ-k (suc k) τ = act-τ suc (weaken-τ-k k τ)

weaken-ε-k : ∀ k → STerm ℓ → STerm (k + ℓ)
weaken-ε-k zero ε = ε
weaken-ε-k (suc k) ε = act-ε suc (weaken-ε-k k ε)


≡-ext : {f₁ f₂ : Fin ℓ → Fin ℓ'}
      → (∀ x → f₁ x ≡ f₂ x)
      → (∀ x → ext f₁ x ≡ ext f₂ x)
≡-ext _ zero = refl
≡-ext x-≡ (suc x) rewrite x-≡ x = refl

var-action-cong : {f₁ f₂ : Fin ℓ → Fin ℓ'}
                → (∀ x → f₁ x ≡ f₂ x)
                → (∀ x → var-action f₁ x ≡ var-action f₂ x)
var-action-cong x-≡ x rewrite x-≡ x = refl

open import Surface.WellScoped.ActionsLemmas var-action-record
                                             record { ≡-ext = ≡-ext
                                                    ; var-action-cong = var-action-cong
                                                    }
                                             public

ext-distr : (r₁ : Fin ℓ₀ → Fin ℓ₁)
          → (r₂ : Fin ℓ₁ → Fin ℓ₂)
          → ∀ x
          → ext r₂ (ext r₁ x) ≡ ext (λ x → r₂ (r₁ x)) x
ext-distr _ _ zero = refl
ext-distr _ _ (suc x) = refl

ActDistributivity : {Ty : ℕ → Set} → ActionOn Ty → Set
ActDistributivity {Ty} act = ∀ {ℓ₀ ℓ₁ ℓ₂}
                             → (r₁ : Fin ℓ₀ → Fin ℓ₁)
                             → (r₂ : Fin ℓ₁ → Fin ℓ₂)
                             → (v : Ty ℓ₀)
                             → act r₂ (act r₁ v) ≡ act (r₂ ∘ r₁) v

act-τ-distr : ActDistributivity act-τ
act-ρ-distr : ActDistributivity act-ρ
act-ε-distr : ActDistributivity act-ε
act-cons-distr : ActDistributivity {ADTCons nₐ} act-cons
act-branches-distr : ActDistributivity {CaseBranches nₐ} act-branches

act-τ-distr r₁ r₂ ⟨ b ∣ ρ ⟩ rewrite act-ρ-distr (ext r₁) (ext r₂) ρ
                                  | act-ρ-extensionality (ext-distr r₁ r₂) ρ = refl
act-τ-distr r₁ r₂ (τ₁ ⇒ τ₂) rewrite act-τ-distr r₁ r₂ τ₁
                                  | act-τ-distr (ext r₁) (ext r₂) τ₂
                                  | act-τ-extensionality (ext-distr r₁ r₂) τ₂ = refl
act-τ-distr r₁ r₂ (⊍ cons) rewrite act-cons-distr r₁ r₂ cons = refl

act-ρ-distr r₁ r₂ (ε₁ ≈ ε₂) rewrite act-ε-distr r₁ r₂ ε₁
                                  | act-ε-distr r₁ r₂ ε₂ = refl
act-ρ-distr r₁ r₂ (ρ₁ ∧ ρ₂) rewrite act-ρ-distr r₁ r₂ ρ₁
                                  | act-ρ-distr r₁ r₂ ρ₂ = refl

act-ε-distr r₁ r₂ SUnit = refl
act-ε-distr r₁ r₂ (SVar idx) = refl
act-ε-distr r₁ r₂ (SLam τ ε) rewrite act-τ-distr r₁ r₂ τ
                                   | act-ε-distr (ext r₁) (ext r₂) ε
                                   | act-ε-extensionality (ext-distr r₁ r₂) ε = refl
act-ε-distr r₁ r₂ (SApp ε₁ ε₂) rewrite act-ε-distr r₁ r₂ ε₁
                                     | act-ε-distr r₁ r₂ ε₂ = refl
act-ε-distr r₁ r₂ (SCase ε branches) rewrite act-ε-distr r₁ r₂ ε
                                           | act-branches-distr r₁ r₂ branches = refl
act-ε-distr r₁ r₂ (SCon idx ε cons) rewrite act-ε-distr r₁ r₂ ε
                                          | act-cons-distr r₁ r₂ cons = refl

act-cons-distr r₁ r₂ [] = refl
act-cons-distr r₁ r₂ (τ ∷ τs) rewrite act-τ-distr r₁ r₂ τ
                                    | act-cons-distr r₁ r₂ τs = refl

act-branches-distr r₁ r₂ [] = refl
act-branches-distr r₁ r₂ (MkCaseBranch body ∷ bs) rewrite act-ε-distr (ext r₁) (ext r₂) body
                                                        | act-branches-distr r₁ r₂ bs
                                                        | act-ε-extensionality (ext-distr r₁ r₂) body = refl


weaken-τ-comm : ∀ (ρ : Fin ℓ → Fin ℓ') (τ : SType ℓ)
              → act-τ (ext ρ) (weaken-τ τ) ≡ weaken-τ (act-τ ρ τ)
weaken-τ-comm ρ τ rewrite act-τ-distr suc (ext ρ) τ
                        | act-τ-distr ρ suc τ = refl

weaken-ε-comm : ∀ (ρ : Fin ℓ → Fin ℓ') (ε : STerm ℓ)
              → act-ε (ext ρ) (weaken-ε ε) ≡ weaken-ε (act-ε ρ ε)
weaken-ε-comm ρ ε rewrite act-ε-distr suc (ext ρ) ε
                        | act-ε-distr ρ suc ε = refl
