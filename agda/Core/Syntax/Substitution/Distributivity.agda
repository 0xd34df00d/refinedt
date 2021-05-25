-- {-# OPTIONS --safe #-}

module Core.Syntax.Substitution.Distributivity where

open import Data.Fin using (suc; zero)
open import Data.Vec using (_∷_; [])
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Helpers
open import Core.Syntax
open import Core.Syntax.Substitution as S
open import Core.Syntax.Substitution.FromRenaming
import Core.Syntax.Renaming as R
import Core.Syntax.Renaming.Distributivity as R

ρ-σ-Distributivity : {Ty : ℕ → Set} → R.ActionOn Ty → ActionOn Ty → Set
ρ-σ-Distributivity {Ty} ρ-act σ-act = ∀ {ℓ₀ ℓ₁ ℓ₂}
                                      → (ρ : Fin ℓ₁ → Fin ℓ₂)
                                      → (σ : Fin ℓ₀ → CExpr ℓ₁)
                                      → (v : Ty ℓ₀)
                                      → ρ-act ρ (σ-act σ v) ≡ σ-act (R.act-ε ρ ∘ σ) v

ρ-σ-distr-ε : ρ-σ-Distributivity R.act-ε act-ε
ρ-σ-distr-cons : ρ-σ-Distributivity {ADTCons nₐ} R.act-cons act-cons
ρ-σ-distr-branches : ρ-σ-Distributivity {CaseBranches nₐ} R.act-branches act-branches

Rext-ext-commutes : (ρ : Fin ℓ₁ → Fin ℓ₂)
                  → (σ : Fin ℓ₀ → CExpr ℓ₁)
                  → R.act-ε (R.ext ρ) ∘ ext σ f≡ ext (R.act-ε ρ ∘ σ)
Rext-ext-commutes ρ σ zero = refl
Rext-ext-commutes ρ σ (suc ι)
  rewrite R.act-ε-distr suc (R.ext ρ) (σ ι)
        | R.act-ε-distr ρ suc (σ ι)
        = refl

ρ-σ-distr-ε ρ σ (CVar ι) = refl
ρ-σ-distr-ε ρ σ (CSort s) = refl
ρ-σ-distr-ε ρ σ (CΠ τ ε)
  rewrite ρ-σ-distr-ε ρ σ τ
        | ρ-σ-distr-ε (R.ext ρ) (ext σ) ε
        | act-ε-extensionality (Rext-ext-commutes ρ σ) ε
        = refl
ρ-σ-distr-ε ρ σ (CLam τ ε)
  rewrite ρ-σ-distr-ε ρ σ τ
        | ρ-σ-distr-ε (R.ext ρ) (ext σ) ε
        | act-ε-extensionality (Rext-ext-commutes ρ σ) ε
        = refl
ρ-σ-distr-ε ρ σ (CApp ε₁ ε₂)
  rewrite ρ-σ-distr-ε ρ σ ε₁
        | ρ-σ-distr-ε ρ σ ε₂
        = refl
ρ-σ-distr-ε ρ σ Cunit = refl
ρ-σ-distr-ε ρ σ CUnit = refl
ρ-σ-distr-ε ρ σ (CADT cons) rewrite ρ-σ-distr-cons ρ σ cons = refl
ρ-σ-distr-ε ρ σ (CCon ι ε cons)
  rewrite ρ-σ-distr-ε ρ σ ε
        | ρ-σ-distr-cons ρ σ cons
        = refl
ρ-σ-distr-ε ρ σ (CCase ε branches)
  rewrite ρ-σ-distr-ε ρ σ ε
        | ρ-σ-distr-branches ρ σ branches
        = refl

ρ-σ-distr-cons ρ σ [] = refl
ρ-σ-distr-cons ρ σ (τ ∷ cons)
  rewrite ρ-σ-distr-ε ρ σ τ
        | ρ-σ-distr-cons ρ σ cons
        = refl

Rext²-ext²-commutes : (ρ : Fin ℓ₁ → Fin ℓ₂)
                    → (σ : Fin ℓ₀ → CExpr ℓ₁)
                    → R.act-ε (R.ext (R.ext ρ)) ∘ ext (ext σ) f≡ ext (ext (R.act-ε ρ ∘ σ))
Rext²-ext²-commutes ρ σ zero = refl
Rext²-ext²-commutes ρ σ (suc zero) = refl
Rext²-ext²-commutes ρ σ (suc (suc ι))
  rewrite R.act-ε-distr suc suc (σ ι)
        | R.act-ε-distr (λ x → suc (suc x)) (R.ext (R.ext ρ)) (σ ι)
        | R.act-ε-distr suc suc (R.act-ε ρ (σ ι))
        | R.act-ε-distr ρ (λ x → suc (suc x)) (σ ι)
        = refl

ρ-σ-distr-branches ρ σ [] = refl
ρ-σ-distr-branches ρ σ (ε ∷ branches)
  rewrite ρ-σ-distr-ε (R.ext (R.ext ρ)) (ext (ext σ)) ε
        | ρ-σ-distr-branches ρ σ branches
        | act-ε-extensionality (Rext²-ext²-commutes ρ σ) ε
        = refl


ActDistributivity : {Ty : ℕ → Set} → ActionOn Ty → Set
ActDistributivity {Ty} act = ∀ {ℓ₀ ℓ₁ ℓ₂}
                             → (σ₁ : Fin ℓ₀ → CExpr ℓ₁)
                             → (σ₂ : Fin ℓ₁ → CExpr ℓ₂)
                             → (v : Ty ℓ₀)
                             → act σ₂ (act σ₁ v) ≡ act (act-ε σ₂ ∘ σ₁) v

act-ε-distr : ActDistributivity act-ε
act-cons-distr : ActDistributivity {ADTCons nₐ} act-cons
act-branches-distr : ActDistributivity {CaseBranches nₐ} act-branches

act-ε-ext-distr : (σ₁ : Fin ℓ₀ → CExpr ℓ₁)
                → (σ₂ : Fin ℓ₁ → CExpr ℓ₂)
                → act-ε (ext σ₂) ∘ ext σ₁ f≡ ext (act-ε σ₂ ∘ σ₁)
act-ε-ext-distr σ₁ σ₂ zero = refl
act-ε-ext-distr σ₁ σ₂ (suc ι)
  rewrite ρ-as-σ-ε suc (σ₁ ι)
        | ρ-as-σ-ε suc (act-ε σ₂ (σ₁ ι))
        | act-ε-distr (λ x → CVar (suc x)) (ext σ₂) (σ₁ ι)
        | act-ε-distr σ₂ (CVar ∘ suc) (σ₁ ι)
        = {! !}

act-ε-distr σ₁ σ₂ (CVar ι) = refl
act-ε-distr σ₁ σ₂ (CSort s) = refl
act-ε-distr σ₁ σ₂ (CΠ τ ε)
  rewrite act-ε-distr σ₁ σ₂ τ
        | act-ε-distr (ext σ₁) (ext σ₂) ε
        | act-ε-extensionality (act-ε-ext-distr σ₁ σ₂) ε
        = refl
act-ε-distr σ₁ σ₂ (CLam τ ε)
  rewrite act-ε-distr σ₁ σ₂ τ
        | act-ε-distr (ext σ₁) (ext σ₂) ε
        | act-ε-extensionality (act-ε-ext-distr σ₁ σ₂) ε
        = refl
act-ε-distr σ₁ σ₂ (CApp ε₁ ε₂)
  rewrite act-ε-distr σ₁ σ₂ ε₁
        | act-ε-distr σ₁ σ₂ ε₂
        = refl
act-ε-distr σ₁ σ₂ Cunit = refl
act-ε-distr σ₁ σ₂ CUnit = refl
act-ε-distr σ₁ σ₂ (CADT cons) rewrite act-cons-distr σ₁ σ₂ cons = refl
act-ε-distr σ₁ σ₂ (CCon ι ε cons)
  rewrite act-ε-distr σ₁ σ₂ ε
        | act-cons-distr σ₁ σ₂ cons
        = refl
act-ε-distr σ₁ σ₂ (CCase ε branches)
  rewrite act-ε-distr σ₁ σ₂ ε
        | act-branches-distr σ₁ σ₂ branches
        = refl

act-cons-distr σ₁ σ₂ [] = refl
act-cons-distr σ₁ σ₂ (τ ∷ cons)
  rewrite act-ε-distr σ₁ σ₂ τ
        | act-cons-distr σ₁ σ₂ cons
        = refl

suc²-distr : (σ₁ : Fin ℓ₀ → CExpr ℓ₁)
      → (σ₂ : Fin ℓ₁ → CExpr ℓ₂)
      → R.act-ε suc ∘ R.act-ε suc ∘ σ₂ f≡ act-ε (λ x → CVar (suc (suc x))) ∘ σ₂
suc²-distr σ₁ σ₂ ι
  rewrite R.act-ε-distr suc suc (σ₂ ι)
        | ρ-as-σ-ε (λ x → suc (suc x)) (σ₂ ι)
        = refl

act-ε-ext²-distr : (σ₁ : Fin ℓ₀ → CExpr ℓ₁)
                 → (σ₂ : Fin ℓ₁ → CExpr ℓ₂)
                 → act-ε (ext (ext σ₂)) ∘ ext (ext σ₁) f≡ ext (ext (act-ε σ₂ ∘ σ₁))
act-ε-ext²-distr σ₁ σ₂ zero = refl
act-ε-ext²-distr σ₁ σ₂ (suc zero) = refl
act-ε-ext²-distr σ₁ σ₂ (suc (suc ι))
  rewrite R.act-ε-distr suc suc (σ₁ ι)
        | R.act-ε-distr suc suc (act-ε σ₂ (σ₁ ι))
        | ρ-as-σ-ε (λ x → suc (suc x)) (σ₁ ι)
        | ρ-as-σ-ε (λ x → suc (suc x)) (act-ε σ₂ (σ₁ ι))
        | act-ε-distr (λ x → CVar (suc (suc x))) (ext (ext σ₂)) (σ₁ ι)
        | act-ε-distr σ₂ (λ x → CVar (suc (suc x))) (σ₁ ι)
        | act-ε-extensionality (suc²-distr σ₁ σ₂) (σ₁ ι)
        = refl

act-branches-distr σ₁ σ₂ [] = refl
act-branches-distr σ₁ σ₂ (ε ∷ branches)
  rewrite act-ε-distr (ext (ext σ₁)) (ext (ext σ₂)) ε
        | act-ε-extensionality (act-ε-ext²-distr σ₁ σ₂) ε
        | act-branches-distr σ₁ σ₂ branches
        = refl
