{-# OPTIONS --safe #-}

module Core.Syntax.Derived.Renaming where

open import Data.Fin using (zero; suc)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Helpers
open import Core.Syntax
open import Core.Syntax.Renaming
open import Core.Syntax.Renaming.Distributivity
open import Core.Syntax.Derived

ext-f∘suc-≡-suc∘f : ∀ (f : Fin ℓ → Fin ℓ')
                  → act-ε (ext f) ∘ act-ε suc f≡ act-ε suc ∘ act-ε f
ext-f∘suc-≡-suc∘f f ε
  rewrite act-ε-distr suc (ext f) ε
        | act-ε-distr f suc ε
        = refl

ext²-f∘suc²-≡-suc²∘f : ∀ (f : Fin ℓ → Fin ℓ')
                     → act-ε (ext (ext f)) ∘ act-ε suc ∘ act-ε suc f≡ act-ε suc ∘ act-ε suc ∘ act-ε f
ext²-f∘suc²-≡-suc²∘f f ε
  rewrite ext-f∘suc-≡-suc∘f (ext f) (act-ε suc ε)
        | ext-f∘suc-≡-suc∘f f ε
        = refl

act-Σ-commutes : ∀ (f : Fin ℓ → Fin ℓ') τ P
               → act-ε f (Σ[ τ ] P) ≡ Σ[ act-ε f τ ] (act-ε f P)
act-Σ-commutes f τ P
  rewrite ext-f∘suc-≡-suc∘f f τ
        | ext²-f∘suc²-≡-suc²∘f f P
        = refl

act-×-commutes : ∀ (f : Fin ℓ → Fin ℓ') τ₁ τ₂
               → act-ε f ⟨ τ₁ × τ₂ ⟩ ≡ ⟨ act-ε f τ₁ × act-ε f τ₂ ⟩
act-×-commutes f τ₁ τ₂
  rewrite ext-f∘suc-≡-suc∘f f τ₁
        | ext²-f∘suc²-≡-suc²∘f f τ₂
        = refl

act-⇒'-commutes : ∀ (f : Fin ℓ → Fin ℓ') τ₁ τ₂
                → act-ε f (τ₁ ⇒' τ₂) ≡ (act-ε f τ₁ ⇒' act-ε f τ₂)
act-⇒'-commutes f τ₁ τ₂ rewrite ext-f∘suc-≡-suc∘f f τ₂ = refl

act-≡̂-commutes : ∀ (f : Fin ℓ → Fin ℓ') ε₁ ε₂ τ
               → act-ε f (ε₁ ≡̂ ε₂ of τ) ≡ (act-ε f ε₁ ≡̂ act-ε f ε₂ of act-ε f τ)
act-≡̂-commutes f ε₁ ε₂ τ
  rewrite act-×-commutes (ext f) (CVar zero · weaken-ε ε₁ ⇒' CVar zero · weaken-ε ε₂) (CVar zero · weaken-ε ε₂ ⇒' CVar zero · weaken-ε ε₁)
        | act-⇒'-commutes (ext f) (CVar zero · weaken-ε ε₁) (CVar zero · weaken-ε ε₂)
        | act-⇒'-commutes (ext f) (CVar zero · weaken-ε ε₂) (CVar zero · weaken-ε ε₁)
        | ext-f∘suc-≡-suc∘f f ε₁
        | ext-f∘suc-≡-suc∘f f ε₂
        | ext²-f∘suc²-≡-suc²∘f f ε₂
        | ext²-f∘suc²-≡-suc²∘f f ε₁
        = refl
