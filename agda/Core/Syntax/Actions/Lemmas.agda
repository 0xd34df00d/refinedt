{-# OPTIONS --safe #-}

open import Core.Syntax

module Core.Syntax.Actions.Lemmas (act : VarAction) (props : VarActionProps act) where

open import Data.Vec using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Syntax.Actions act
open VarActionProps props

ActExtensionality : {Ty : ℕ → Set} → ActionOn Ty → Set
ActExtensionality {Ty} act = ∀ {ℓ ℓ'}
                             → {f₁ f₂ : Fin ℓ → Target ℓ'}
                             → ((x : Fin ℓ) → f₁ x ≡ f₂ x)
                             → (v : Ty ℓ)
                             → act f₁ v ≡ act f₂ v

act-ε-extensionality : ActExtensionality act-ε
act-cons-extensionality : ActExtensionality {ADTCons nₐ} act-cons
act-branches-extensionality : ActExtensionality {CaseBranches nₐ} act-branches

act-ε-extensionality x-≡ (CVar ι) rewrite x-≡ ι = refl
act-ε-extensionality x-≡ (CSort s) = refl
act-ε-extensionality x-≡ (CΠ τ₁ τ₂)
  rewrite act-ε-extensionality x-≡ τ₁
        | act-ε-extensionality (≡-ext x-≡) τ₂
        = refl
act-ε-extensionality x-≡ (CLam τ ε)
  rewrite act-ε-extensionality x-≡ τ
        | act-ε-extensionality (≡-ext x-≡) ε
        = refl
act-ε-extensionality x-≡ (CApp ε₁ ε₂)
  rewrite act-ε-extensionality x-≡ ε₁
        | act-ε-extensionality x-≡ ε₂
        = refl
act-ε-extensionality x-≡ Cunit = refl
act-ε-extensionality x-≡ CUnit = refl
act-ε-extensionality x-≡ (CADT cons) rewrite act-cons-extensionality x-≡ cons = refl
act-ε-extensionality x-≡ (CCon ι ε cons)
  rewrite act-ε-extensionality x-≡ ε
        | act-cons-extensionality x-≡ cons
        = refl
act-ε-extensionality x-≡ (CCase ε branches)
  rewrite act-ε-extensionality x-≡ ε
        | act-branches-extensionality x-≡ branches
        = refl

act-cons-extensionality x-≡ [] = refl
act-cons-extensionality x-≡ (τ ∷ cons)
  rewrite act-ε-extensionality x-≡ τ
        | act-cons-extensionality x-≡ cons
        = refl

act-branches-extensionality x-≡ [] = refl
act-branches-extensionality x-≡ (ε ∷ branches)
  rewrite act-ε-extensionality (≡-ext (≡-ext x-≡)) ε
        | act-branches-extensionality x-≡ branches
        = refl
