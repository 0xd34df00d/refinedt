{-# OPTIONS --safe #-}

module Surface.WellScoped.Substitution.Distributivity where

open import Data.Fin using (Fin; suc; zero; raise)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Vec
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.WellScoped
open import Surface.WellScoped.Substitution as S
import Surface.WellScoped.Renaming as R

Rename-σ-Distributivity : {Ty : ℕ → Set} → R.ActionOn Ty → ActionOn Ty → Set
Rename-σ-Distributivity {Ty} ρ-act σ-act = ∀ {ℓ₀ ℓ₁ ℓ₂}
                                           → (ρ : Fin ℓ₁ → Fin ℓ₂)
                                           → (σ : Fin ℓ₀ → STerm ℓ₁)
                                           → (v : Ty ℓ₀)
                                           → ρ-act ρ (σ-act σ v) ≡ σ-act (R.act-ε ρ ∘ σ) v

rename-σ-distr-τ : Rename-σ-Distributivity R.act-τ act-τ
rename-σ-distr-ρ : Rename-σ-Distributivity R.act-ρ act-ρ
rename-σ-distr-ε : Rename-σ-Distributivity R.act-ε act-ε
rename-σ-distr-cons : Rename-σ-Distributivity {ADTCons nₐ} R.act-cons act-cons
rename-σ-distr-branches : Rename-σ-Distributivity {CaseBranches nₐ} R.act-branches act-branches

R-ext-ext-commutes-ε : (ρ : Fin ℓ₁ → Fin ℓ₂)
                     → (σ : Fin ℓ₀ → STerm ℓ₁)
                     → ∀ x → R.act-ε (R.ext ρ) (ext σ x) ≡ ext (R.act-ε ρ ∘ σ) x
R-ext-ext-commutes-ε ρ σ zero = refl
R-ext-ext-commutes-ε ρ σ (suc x) rewrite R.act-ε-distr suc (R.ext ρ) (σ x)
                                       | R.act-ε-distr ρ suc (σ x)
                                       = refl

rename-σ-distr-τ ρ σ ⟨ b ∣ ρ' ⟩ rewrite rename-σ-distr-ρ (R.ext ρ) (ext σ) ρ'
                                      | act-ρ-extensionality (R-ext-ext-commutes-ε ρ σ) ρ'
                                      = refl
rename-σ-distr-τ ρ σ (τ₁ ⇒ τ₂) rewrite rename-σ-distr-τ ρ σ τ₁
                                     | rename-σ-distr-τ (R.ext ρ) (ext σ) τ₂
                                     | act-τ-extensionality (R-ext-ext-commutes-ε ρ σ) τ₂
                                     = refl
rename-σ-distr-τ ρ σ (⊍ cons) rewrite rename-σ-distr-cons ρ σ cons = refl

rename-σ-distr-ρ ρ σ (ε₁ ≈ ε₂) rewrite rename-σ-distr-ε ρ σ ε₁
                                     | rename-σ-distr-ε ρ σ ε₂
                                     = refl
rename-σ-distr-ρ ρ σ (ρ₁ ∧ ρ₂) rewrite rename-σ-distr-ρ ρ σ ρ₁
                                     | rename-σ-distr-ρ ρ σ ρ₂
                                     = refl

rename-σ-distr-ε ρ σ SUnit = refl
rename-σ-distr-ε ρ σ (SVar idx) = refl
rename-σ-distr-ε ρ σ (SLam τ ε) rewrite rename-σ-distr-τ ρ σ τ
                                      | rename-σ-distr-ε (R.ext ρ) (ext σ) ε
                                      | act-ε-extensionality (R-ext-ext-commutes-ε ρ σ) ε
                                      = refl
rename-σ-distr-ε ρ σ (SApp ε₁ ε₂) rewrite rename-σ-distr-ε ρ σ ε₁
                                        | rename-σ-distr-ε ρ σ ε₂
                                        = refl
rename-σ-distr-ε ρ σ (SCase ε branches) rewrite rename-σ-distr-ε ρ σ ε
                                              | rename-σ-distr-branches ρ σ branches
                                              = refl
rename-σ-distr-ε ρ σ (SCon idx ε cons) rewrite rename-σ-distr-ε ρ σ ε
                                             | rename-σ-distr-cons ρ σ cons
                                             = refl

rename-σ-distr-cons ρ σ [] = refl
rename-σ-distr-cons ρ σ (τ ∷ cons) rewrite rename-σ-distr-τ ρ σ τ
                                         | rename-σ-distr-cons ρ σ cons
                                         = refl

rename-σ-distr-branches ρ σ [] = refl
rename-σ-distr-branches ρ σ (MkCaseBranch ε ∷ bs) rewrite rename-σ-distr-ε (R.ext ρ) (ext σ) ε
                                                        | rename-σ-distr-branches ρ σ bs
                                                        | act-ε-extensionality (R-ext-ext-commutes-ε ρ σ) ε
                                                        = refl


act-ε-ext-distr : (σ₁ : Fin ℓ₀ → STerm ℓ₁)
                → (σ₂ : Fin ℓ₁ → STerm ℓ₂)
                → (x : Fin (suc ℓ₀))
                → act-ε (ext σ₂) (ext σ₁ x) ≡ ext (act-ε σ₂ ∘ σ₁) x
act-ε-ext-distr σ₁ σ₂ zero = refl
act-ε-ext-distr σ₁ σ₂ (suc x) rewrite subst-rename-ε-distr (ext σ₂) suc (σ₁ x)
                                    | rename-σ-distr-ε suc σ₂ (σ₁ x)
                                    = refl

ActDistributivity : {Ty : ℕ → Set} → ActionOn Ty → Set
ActDistributivity {Ty} act = ∀ {ℓ₀ ℓ₁ ℓ₂}
                             → (σ₁ : Fin ℓ₀ → STerm ℓ₁)
                             → (σ₂ : Fin ℓ₁ → STerm ℓ₂)
                             → (v : Ty ℓ₀)
                             → act σ₂ (act σ₁ v) ≡ act (act-ε σ₂ ∘ σ₁) v

act-τ-distr : ActDistributivity act-τ
act-ρ-distr : ActDistributivity act-ρ
act-ε-distr : ActDistributivity act-ε
act-cons-distr : ActDistributivity {ADTCons nₐ} act-cons
act-branches-distr : ActDistributivity {CaseBranches nₐ} act-branches

act-τ-distr σ₁ σ₂ ⟨ b ∣ ρ ⟩ rewrite act-ρ-distr (ext σ₁) (ext σ₂) ρ
                                  | act-ρ-extensionality (act-ε-ext-distr σ₁ σ₂) ρ
                                  = refl
act-τ-distr σ₁ σ₂ (τ₁ ⇒ τ₂) rewrite act-τ-distr σ₁ σ₂ τ₁
                                  | act-τ-distr (ext σ₁) (ext σ₂) τ₂
                                  | act-τ-extensionality (act-ε-ext-distr σ₁ σ₂) τ₂
                                  = refl
act-τ-distr σ₁ σ₂ (⊍ cons) rewrite act-cons-distr σ₁ σ₂ cons = refl

act-ρ-distr σ₁ σ₂ (ε₁ ≈ ε₂) rewrite act-ε-distr σ₁ σ₂ ε₁
                                  | act-ε-distr σ₁ σ₂ ε₂
                                  = refl
act-ρ-distr σ₁ σ₂ (ρ₁ ∧ ρ₂) rewrite act-ρ-distr σ₁ σ₂ ρ₁
                                  | act-ρ-distr σ₁ σ₂ ρ₂
                                  = refl

act-ε-distr σ₁ σ₂ SUnit = refl
act-ε-distr σ₁ σ₂ (SVar idx) = refl
act-ε-distr σ₁ σ₂ (SLam τ ε) rewrite act-τ-distr σ₁ σ₂ τ
                                   | act-ε-distr (ext σ₁) (ext σ₂) ε
                                   | act-ε-extensionality (act-ε-ext-distr σ₁ σ₂) ε
                                   = refl
act-ε-distr σ₁ σ₂ (SApp ε₁ ε₂) rewrite act-ε-distr σ₁ σ₂ ε₁
                                     | act-ε-distr σ₁ σ₂ ε₂
                                     = refl
act-ε-distr σ₁ σ₂ (SCase ε branches) rewrite act-ε-distr σ₁ σ₂ ε
                                           | act-branches-distr σ₁ σ₂ branches
                                           = refl
act-ε-distr σ₁ σ₂ (SCon idx ε cons) rewrite act-ε-distr σ₁ σ₂ ε
                                          | act-cons-distr σ₁ σ₂ cons
                                          = refl

act-cons-distr σ₁ σ₂ [] = refl
act-cons-distr σ₁ σ₂ (τ ∷ cons) rewrite act-τ-distr σ₁ σ₂ τ
                                      | act-cons-distr σ₁ σ₂ cons
                                      = refl

act-branches-distr σ₁ σ₂ [] = refl
act-branches-distr σ₁ σ₂ (MkCaseBranch ε ∷ bs) rewrite act-ε-distr (ext σ₁) (ext σ₂) ε
                                                     | act-ε-extensionality (act-ε-ext-distr σ₁ σ₂) ε
                                                     | act-branches-distr σ₁ σ₂ bs
                                                     = refl
