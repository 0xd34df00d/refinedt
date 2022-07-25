{-# OPTIONS --safe #-}

module Surface.Syntax.Substitution.FromRenaming where

open import Data.Fin using (Fin; suc; zero; raise)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Vec
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.Substitution as S
import Surface.Syntax.Renaming as R

RenamingAsSubst : {Ty : ℕ → Set} → R.ActionOn Ty → S.ActionOn Ty → Set
RenamingAsSubst {Ty} ρ-act σ-act = ∀ {ℓ ℓ'}
                                   → (ρ : Fin ℓ → Fin ℓ')
                                   → (v : Ty ℓ)
                                   → ρ-act ρ v ≡ σ-act (SVar ∘ ρ) v

var-ext-commutes : ∀ (ρ : Fin ℓ → Fin ℓ')
                 → ∀ x → SVar (R.ext ρ x) ≡ ext (SVar ∘ ρ) x
var-ext-commutes ρ zero = refl
var-ext-commutes ρ (suc x) = refl

mutual
  ρ-as-σ-τ : RenamingAsSubst R.act-τ act-τ
  ρ-as-σ-τ ρ ⟨ b ∣ ρ' ⟩
    rewrite ρ-as-σ-ρ (R.ext ρ) ρ'
          | act-ρ-extensionality (var-ext-commutes ρ) ρ'
          = refl
  ρ-as-σ-τ ρ (τ₁ ⇒ τ₂)
    rewrite ρ-as-σ-τ ρ τ₁
          | ρ-as-σ-τ (R.ext ρ) τ₂
          | act-τ-extensionality (var-ext-commutes ρ) τ₂
          = refl
  ρ-as-σ-τ ρ (⊍ cons) rewrite ρ-as-σ-cons ρ cons = refl

  ρ-as-σ-ρ : RenamingAsSubst R.act-ρ act-ρ
  ρ-as-σ-ρ ρ (ε₁ ≈ ε₂ of τ)
    rewrite ρ-as-σ-ε ρ ε₁
          | ρ-as-σ-ε ρ ε₂
          | ρ-as-σ-τ ρ τ
          = refl
  ρ-as-σ-ρ ρ (ρ₁ ∧ ρ₂)
    rewrite ρ-as-σ-ρ ρ ρ₁
          | ρ-as-σ-ρ ρ ρ₂
          = refl
  ρ-as-σ-ρ _ Τ = refl

  ρ-as-σ-ε : RenamingAsSubst R.act-ε act-ε
  ρ-as-σ-ε ρ SUnit = refl
  ρ-as-σ-ε ρ (SVar ι) = refl
  ρ-as-σ-ε ρ (SLam τ ε)
    rewrite ρ-as-σ-τ ρ τ
          | ρ-as-σ-ε (R.ext ρ) ε
          | act-ε-extensionality (var-ext-commutes ρ) ε
          = refl
  ρ-as-σ-ε ρ (SApp ε₁ ε₂)
    rewrite ρ-as-σ-ε ρ ε₁
          | ρ-as-σ-ε ρ ε₂
          = refl
  ρ-as-σ-ε ρ (SCase ε cons τ branches)
    rewrite ρ-as-σ-ε ρ ε
          | ρ-as-σ-cons ρ cons
          | ρ-as-σ-τ ρ τ
          | ρ-as-σ-branches ρ branches
          = refl
  ρ-as-σ-ε ρ (SCon ι ε cons)
    rewrite ρ-as-σ-ε ρ ε
          | ρ-as-σ-cons ρ cons
          = refl

  ρ-as-σ-cons : RenamingAsSubst {ADTCons nₐ} R.act-cons act-cons
  ρ-as-σ-cons ρ [] = refl
  ρ-as-σ-cons ρ (τ ∷ cons)
    rewrite ρ-as-σ-τ ρ τ
          | ρ-as-σ-cons ρ cons
          = refl

  ρ-as-σ-branches : RenamingAsSubst {CaseBranches nₐ} R.act-branches act-branches
  ρ-as-σ-branches ρ [] = refl
  ρ-as-σ-branches ρ (MkCaseBranch ε ∷ bs)
    rewrite ρ-as-σ-ε (R.ext ρ) ε
          | act-ε-extensionality (var-ext-commutes ρ) ε
          | ρ-as-σ-branches ρ bs
          = refl
