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

ρ-σ-Distributivity : {Ty : ℕ → Set} → R.ActionOn Ty → ActionOn Ty → Set
ρ-σ-Distributivity {Ty} ρ-act σ-act = ∀ {ℓ₀ ℓ₁ ℓ₂}
                                      → (ρ : Fin ℓ₁ → Fin ℓ₂)
                                      → (σ : Fin ℓ₀ → STerm ℓ₁)
                                      → (v : Ty ℓ₀)
                                      → ρ-act ρ (σ-act σ v) ≡ σ-act (R.act-ε ρ ∘ σ) v

ρ-σ-distr-τ : ρ-σ-Distributivity R.act-τ act-τ
ρ-σ-distr-ρ : ρ-σ-Distributivity R.act-ρ act-ρ
ρ-σ-distr-ε : ρ-σ-Distributivity R.act-ε act-ε
ρ-σ-distr-cons : ρ-σ-Distributivity {ADTCons nₐ} R.act-cons act-cons
ρ-σ-distr-branches : ρ-σ-Distributivity {CaseBranches nₐ} R.act-branches act-branches

R-ext-ext-commutes-ε : (ρ : Fin ℓ₁ → Fin ℓ₂)
                     → (σ : Fin ℓ₀ → STerm ℓ₁)
                     → ∀ x → R.act-ε (R.ext ρ) (ext σ x) ≡ ext (R.act-ε ρ ∘ σ) x
R-ext-ext-commutes-ε ρ σ zero = refl
R-ext-ext-commutes-ε ρ σ (suc x) rewrite R.act-ε-distr suc (R.ext ρ) (σ x)
                                       | R.act-ε-distr ρ suc (σ x)
                                       = refl

ρ-σ-distr-τ ρ σ ⟨ b ∣ ρ' ⟩ rewrite ρ-σ-distr-ρ (R.ext ρ) (ext σ) ρ'
                                 | act-ρ-extensionality (R-ext-ext-commutes-ε ρ σ) ρ'
                                 = refl
ρ-σ-distr-τ ρ σ (τ₁ ⇒ τ₂) rewrite ρ-σ-distr-τ ρ σ τ₁
                                | ρ-σ-distr-τ (R.ext ρ) (ext σ) τ₂
                                | act-τ-extensionality (R-ext-ext-commutes-ε ρ σ) τ₂
                                = refl
ρ-σ-distr-τ ρ σ (⊍ cons) rewrite ρ-σ-distr-cons ρ σ cons = refl

ρ-σ-distr-ρ ρ σ (ε₁ ≈ ε₂) rewrite ρ-σ-distr-ε ρ σ ε₁
                                | ρ-σ-distr-ε ρ σ ε₂
                                = refl
ρ-σ-distr-ρ ρ σ (ρ₁ ∧ ρ₂) rewrite ρ-σ-distr-ρ ρ σ ρ₁
                                | ρ-σ-distr-ρ ρ σ ρ₂
                                = refl

ρ-σ-distr-ε ρ σ SUnit = refl
ρ-σ-distr-ε ρ σ (SVar idx) = refl
ρ-σ-distr-ε ρ σ (SLam τ ε) rewrite ρ-σ-distr-τ ρ σ τ
                                 | ρ-σ-distr-ε (R.ext ρ) (ext σ) ε
                                 | act-ε-extensionality (R-ext-ext-commutes-ε ρ σ) ε
                                 = refl
ρ-σ-distr-ε ρ σ (SApp ε₁ ε₂) rewrite ρ-σ-distr-ε ρ σ ε₁
                                   | ρ-σ-distr-ε ρ σ ε₂
                                   = refl
ρ-σ-distr-ε ρ σ (SCase ε branches) rewrite ρ-σ-distr-ε ρ σ ε
                                         | ρ-σ-distr-branches ρ σ branches
                                         = refl
ρ-σ-distr-ε ρ σ (SCon idx ε cons) rewrite ρ-σ-distr-ε ρ σ ε
                                        | ρ-σ-distr-cons ρ σ cons
                                        = refl

ρ-σ-distr-cons ρ σ [] = refl
ρ-σ-distr-cons ρ σ (τ ∷ cons) rewrite ρ-σ-distr-τ ρ σ τ
                                    | ρ-σ-distr-cons ρ σ cons
                                    = refl

ρ-σ-distr-branches ρ σ [] = refl
ρ-σ-distr-branches ρ σ (MkCaseBranch ε ∷ bs) rewrite ρ-σ-distr-ε (R.ext ρ) (ext σ) ε
                                                   | ρ-σ-distr-branches ρ σ bs
                                                   | act-ε-extensionality (R-ext-ext-commutes-ε ρ σ) ε
                                                   = refl

σ-ρ-Distributivity : {Ty : ℕ → Set} → ActionOn Ty → R.ActionOn Ty → Set
σ-ρ-Distributivity {Ty} σ-act ρ-act = ∀ {ℓ₀ ℓ₁ ℓ₂}
                                      → (σ : Fin ℓ₁ → STerm ℓ₂)
                                      → (ρ : Fin ℓ₀ → Fin ℓ₁)
                                      → (v : Ty ℓ₀)
                                      → σ-act σ (ρ-act ρ v) ≡ σ-act (σ ∘ ρ) v

ext-Rext-distr : (σ : Fin ℓ₁ → STerm ℓ₂)
               → (ρ : Fin ℓ₀ → Fin ℓ₁)
               → (∀ x → ext σ (R.ext ρ x) ≡ ext (σ ∘ ρ) x)
ext-Rext-distr σ ρ zero = refl
ext-Rext-distr σ ρ (suc x) = refl

σ-ρ-distr-τ : σ-ρ-Distributivity act-τ R.act-τ
σ-ρ-distr-ρ : σ-ρ-Distributivity act-ρ R.act-ρ
σ-ρ-distr-ε : σ-ρ-Distributivity act-ε R.act-ε
σ-ρ-distr-cons : σ-ρ-Distributivity {ADTCons nₐ} act-cons R.act-cons
σ-ρ-distr-branches : σ-ρ-Distributivity {CaseBranches nₐ} act-branches R.act-branches

σ-ρ-distr-τ σ ρ ⟨ b ∣ ρ' ⟩ rewrite σ-ρ-distr-ρ (ext σ) (R.ext ρ) ρ'
                                 | act-ρ-extensionality (ext-Rext-distr σ ρ) ρ'
                                 = refl
σ-ρ-distr-τ σ ρ (τ₁ ⇒ τ₂) rewrite σ-ρ-distr-τ σ ρ τ₁
                                | σ-ρ-distr-τ (ext σ) (R.ext ρ) τ₂
                                | act-τ-extensionality (ext-Rext-distr σ ρ) τ₂
                                = refl
σ-ρ-distr-τ σ ρ (⊍ cons) rewrite σ-ρ-distr-cons σ ρ cons = refl

σ-ρ-distr-ρ σ ρ (ε₁ ≈ ε₂) rewrite σ-ρ-distr-ε σ ρ ε₁
                                | σ-ρ-distr-ε σ ρ ε₂
                                = refl
σ-ρ-distr-ρ σ ρ (ρ₁ ∧ ρ₂) rewrite σ-ρ-distr-ρ σ ρ ρ₁
                                | σ-ρ-distr-ρ σ ρ ρ₂
                                = refl

σ-ρ-distr-ε σ ρ SUnit = refl
σ-ρ-distr-ε σ ρ (SVar idx) = refl
σ-ρ-distr-ε σ ρ (SLam τ ε) rewrite σ-ρ-distr-τ σ ρ τ
                                 | σ-ρ-distr-ε (ext σ) (R.ext ρ) ε
                                 | act-ε-extensionality (ext-Rext-distr σ ρ) ε
                                 = refl
σ-ρ-distr-ε σ ρ (SApp ε₁ ε₂) rewrite σ-ρ-distr-ε σ ρ ε₁
                                   | σ-ρ-distr-ε σ ρ ε₂
                                   = refl
σ-ρ-distr-ε σ ρ (SCase ε branches) rewrite σ-ρ-distr-ε σ ρ ε
                                         | σ-ρ-distr-branches σ ρ branches
                                         = refl
σ-ρ-distr-ε σ ρ (SCon idx ε cons) rewrite σ-ρ-distr-ε σ ρ ε
                                        | σ-ρ-distr-cons σ ρ cons
                                        = refl

σ-ρ-distr-cons σ ρ [] = refl
σ-ρ-distr-cons σ ρ (τ ∷ cons) rewrite σ-ρ-distr-τ σ ρ τ
                                    | σ-ρ-distr-cons σ ρ cons
                                    = refl

σ-ρ-distr-branches σ ρ [] = refl
σ-ρ-distr-branches σ ρ (MkCaseBranch ε ∷ bs) rewrite σ-ρ-distr-ε (ext σ) (R.ext ρ) ε
                                                   | σ-ρ-distr-branches σ ρ bs
                                                   | act-ε-extensionality (ext-Rext-distr σ ρ) ε
                                                   = refl


act-ε-ext-distr : (σ₁ : Fin ℓ₀ → STerm ℓ₁)
                → (σ₂ : Fin ℓ₁ → STerm ℓ₂)
                → (x : Fin (suc ℓ₀))
                → act-ε (ext σ₂) (ext σ₁ x) ≡ ext (act-ε σ₂ ∘ σ₁) x
act-ε-ext-distr σ₁ σ₂ zero = refl
act-ε-ext-distr σ₁ σ₂ (suc x) rewrite σ-ρ-distr-ε (ext σ₂) suc (σ₁ x)
                                    | ρ-σ-distr-ε suc σ₂ (σ₁ x)
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