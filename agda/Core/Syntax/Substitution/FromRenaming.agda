{-# OPTIONS --safe #-}

module Core.Syntax.Substitution.FromRenaming where

open import Data.Fin using (zero; suc)
open import Data.Vec using (_∷_; [])
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Helpers
open import Core.Syntax
open import Core.Syntax.Substitution as S
import Core.Syntax.Renaming as R

RenamingAsSubst : {Ty : ℕ → Set} → R.ActionOn Ty → S.ActionOn Ty → Set
RenamingAsSubst {Ty} ρ-act σ-act = ∀ {ℓ ℓ'}
                                   → (ρ : Fin ℓ → Fin ℓ')
                                   → (v : Ty ℓ)
                                   → ρ-act ρ v ≡ σ-act (CVar ∘ ρ) v

ρ-as-σ-ε : RenamingAsSubst R.act-ε act-ε
ρ-as-σ-cons : RenamingAsSubst {ADTCons nₐ} R.act-cons act-cons
ρ-as-σ-branches : RenamingAsSubst {CaseBranches nₐ} R.act-branches act-branches

var-ext-commutes : (ρ : Fin ℓ → Fin ℓ')
                 → CVar ∘ R.ext ρ f≡ ext (CVar ∘ ρ)
var-ext-commutes ρ zero = refl
var-ext-commutes ρ (suc ι) = refl

var-ext²-commutes : (ρ : Fin ℓ → Fin ℓ')
                  → CVar ∘ R.ext (R.ext ρ) f≡ ext (ext (CVar ∘ ρ))
var-ext²-commutes ρ zero = refl
var-ext²-commutes ρ (suc zero) = refl
var-ext²-commutes ρ (suc (suc ι)) = refl

ρ-as-σ-ε ρ (CVar ι) = refl
ρ-as-σ-ε ρ (CSort s) = refl
ρ-as-σ-ε ρ (CΠ τ₁ τ₂)
  rewrite ρ-as-σ-ε ρ τ₁
        | ρ-as-σ-ε (R.ext ρ) τ₂
        | act-ε-extensionality (var-ext-commutes ρ) τ₂
        = refl
ρ-as-σ-ε ρ (CLam τ ε)
  rewrite ρ-as-σ-ε ρ τ
        | ρ-as-σ-ε (R.ext ρ) ε
        | act-ε-extensionality (var-ext-commutes ρ) ε
        = refl
ρ-as-σ-ε ρ (CApp ε₁ ε₂)
  rewrite ρ-as-σ-ε ρ ε₁
        | ρ-as-σ-ε ρ ε₂
        = refl
ρ-as-σ-ε ρ Cunit = refl
ρ-as-σ-ε ρ CUnit = refl
ρ-as-σ-ε ρ (CADT cons) rewrite ρ-as-σ-cons ρ cons = refl
ρ-as-σ-ε ρ (CCon ι ε cons)
  rewrite ρ-as-σ-ε ρ ε
        | ρ-as-σ-cons ρ cons
        = refl
ρ-as-σ-ε ρ (CCase ε branches)
  rewrite ρ-as-σ-ε ρ ε
        | ρ-as-σ-branches ρ branches
        = refl

ρ-as-σ-cons ρ [] = refl
ρ-as-σ-cons ρ (τ ∷ cons)
  rewrite ρ-as-σ-ε ρ τ
        | ρ-as-σ-cons ρ cons
        = refl

ρ-as-σ-branches ρ [] = refl
ρ-as-σ-branches ρ (ε ∷ bs)
  rewrite ρ-as-σ-ε (R.ext (R.ext ρ)) ε
        | act-ε-extensionality (var-ext²-commutes ρ) ε
        | ρ-as-σ-branches ρ bs
        = refl
