{-# OPTIONS --safe #-}

module Core.Syntax.Renaming.Distributivity where

open import Data.Fin using (suc; zero)
open import Data.Vec using (_∷_; [])
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Helpers
open import Core.Syntax
open import Core.Syntax.Renaming

ActDistributivity : {Ty : ℕ → Set} → ActionOn Ty → Set
ActDistributivity {Ty} act = ∀ {ℓ₀ ℓ₁ ℓ₂}
                             → (ρ₁ : Fin ℓ₀ → Fin ℓ₁)
                             → (ρ₂ : Fin ℓ₁ → Fin ℓ₂)
                             → (v : Ty ℓ₀)
                             → act ρ₂ (act ρ₁ v) ≡ act (ρ₂ ∘ ρ₁) v

act-ε-distr : ActDistributivity act-ε
act-cons-distr : ActDistributivity {ADTCons nₐ} act-cons
act-branches-distr : ActDistributivity {CaseBranches nₐ} act-branches

act-ε-distr ρ₁ ρ₂ (CVar ι) = refl
act-ε-distr ρ₁ ρ₂ (CSort s) = refl
act-ε-distr ρ₁ ρ₂ (CΠ τ₁ τ₂)
  rewrite act-ε-distr ρ₁ ρ₂ τ₁
        | act-ε-distr (ext ρ₁) (ext ρ₂) τ₂
        | act-ε-extensionality (ext-distr ρ₁ ρ₂) τ₂
        = refl
act-ε-distr ρ₁ ρ₂ (CLam τ ε)
  rewrite act-ε-distr ρ₁ ρ₂ τ
        | act-ε-distr (ext ρ₁) (ext ρ₂) ε
        | act-ε-extensionality (ext-distr ρ₁ ρ₂) ε
        = refl
act-ε-distr ρ₁ ρ₂ (CApp ε₁ ε₂)
  rewrite act-ε-distr ρ₁ ρ₂ ε₁
        | act-ε-distr ρ₁ ρ₂ ε₂
        = refl
act-ε-distr ρ₁ ρ₂ Cunit = refl
act-ε-distr ρ₁ ρ₂ CUnit = refl
act-ε-distr ρ₁ ρ₂ (CADT cons) rewrite act-cons-distr ρ₁ ρ₂ cons = refl
act-ε-distr ρ₁ ρ₂ (CCon ι ε cons)
  rewrite act-ε-distr ρ₁ ρ₂ ε
        | act-cons-distr ρ₁ ρ₂ cons
        = refl
act-ε-distr ρ₁ ρ₂ (CCase ε branches)
  rewrite act-ε-distr ρ₁ ρ₂ ε
        | act-branches-distr ρ₁ ρ₂ branches
        = refl

act-cons-distr ρ₁ ρ₂ [] = refl
act-cons-distr ρ₁ ρ₂ (τ ∷ cons)
  rewrite act-ε-distr ρ₁ ρ₂ τ
        | act-cons-distr ρ₁ ρ₂ cons
        = refl

ext²-distr : (ρ₁ : Fin ℓ₀ → Fin ℓ₁)
           → (ρ₂ : Fin ℓ₁ → Fin ℓ₂)
           → ext (ext ρ₂) ∘ ext (ext ρ₁) f≡ ext (ext (ρ₂ ∘ ρ₁))
ext²-distr ρ₁ ρ₂ zero = refl
ext²-distr ρ₁ ρ₂ (suc zero) = refl
ext²-distr ρ₁ ρ₂ (suc (suc ι)) = refl

act-branches-distr ρ₁ ρ₂ [] = refl
act-branches-distr ρ₁ ρ₂ (ε ∷ branches)
  rewrite act-ε-distr (ext (ext ρ₁)) (ext (ext ρ₂)) ε
        | act-ε-extensionality (ext²-distr ρ₁ ρ₂) ε
        | act-branches-distr ρ₁ ρ₂ branches
        = refl
