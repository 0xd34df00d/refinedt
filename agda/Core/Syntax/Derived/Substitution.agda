{-# OPTIONS --safe #-}

module Core.Syntax.Derived.Substitution where

open import Data.Fin using (Fin; zero; suc)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Helpers
open import Core.Syntax
open import Core.Syntax.Renaming as R
open import Core.Syntax.Substitution as S
open import Core.Syntax.Substitution.Distributivity
open import Core.Syntax.Derived

ext-f∘suc-≡-suc∘f : (f : Fin ℓ → CExpr ℓ')
                  → S.act-ε (S.ext f) ∘ R.act-ε suc f≡ R.act-ε suc ∘ S.act-ε f
ext-f∘suc-≡-suc∘f f ε
  rewrite σ-ρ-distr-ε (S.ext f) suc ε
        | ρ-σ-distr-ε suc f ε
        = refl

ext²-f∘suc²-≡-suc²∘f : (f : Fin ℓ → CExpr ℓ')
                     → S.act-ε (S.ext (S.ext f)) ∘ R.act-ε suc ∘ R.act-ε suc f≡ R.act-ε suc ∘ R.act-ε suc ∘ S.act-ε f
ext²-f∘suc²-≡-suc²∘f f ε
  rewrite ext-f∘suc-≡-suc∘f (S.ext f) (R.act-ε suc ε)
        | ext-f∘suc-≡-suc∘f f ε
        = refl

act-Σ-commutes : ∀ (f : Fin ℓ → CExpr ℓ') τ P
               → S.act-ε f (Σ[ τ ] P) ≡ Σ[ S.act-ε f τ ] (S.act-ε f P)
act-Σ-commutes f τ P
  rewrite ext-f∘suc-≡-suc∘f f τ
        | ext²-f∘suc²-≡-suc²∘f f P
        = refl

act-×-commutes : ∀ (f : Fin ℓ → CExpr ℓ') τ₁ τ₂
               → S.act-ε f ⟨ τ₁ × τ₂ ⟩ ≡ ⟨ S.act-ε f τ₁ × S.act-ε f τ₂ ⟩
act-×-commutes f τ₁ τ₂
  rewrite ext-f∘suc-≡-suc∘f f τ₁
        | ext²-f∘suc²-≡-suc²∘f f τ₂
        = refl

act-⇒'-commutes : ∀ (f : Fin ℓ → CExpr ℓ') τ₁ τ₂
                → S.act-ε f (τ₁ ⇒' τ₂) ≡ (S.act-ε f τ₁ ⇒' S.act-ε f τ₂)
act-⇒'-commutes f τ₁ τ₂ rewrite ext-f∘suc-≡-suc∘f f τ₂ = refl

act-≡̂-commutes : ∀ (f : Fin ℓ → CExpr ℓ') ε₁ ε₂ τ
               → S.act-ε f (ε₁ ≡̂ ε₂ of τ) ≡ (S.act-ε f ε₁ ≡̂ S.act-ε f ε₂ of S.act-ε f τ)
act-≡̂-commutes f ε₁ ε₂ τ
  rewrite act-×-commutes (S.ext f) (CVar zero · weaken-ε ε₁ ⇒' CVar zero · weaken-ε ε₂) (CVar zero · weaken-ε ε₂ ⇒' CVar zero · weaken-ε ε₁)
        | act-⇒'-commutes (S.ext f) (CVar zero · weaken-ε ε₁) (CVar zero · weaken-ε ε₂)
        | act-⇒'-commutes (S.ext f) (CVar zero · weaken-ε ε₂) (CVar zero · weaken-ε ε₁)
        | ext-f∘suc-≡-suc∘f f ε₁
        | ext-f∘suc-≡-suc∘f f ε₂
        | ext²-f∘suc²-≡-suc²∘f f ε₂
        | ext²-f∘suc²-≡-suc²∘f f ε₁
        = refl


×-↦'-distr : ∀ ℓ (ε : CExpr ℓ) (ε₁ ε₂ : CExpr (suc k + ℓ))
           → [ ℓ ↦' ε ] ⟨ ε₁ × ε₂ ⟩ ≡ ⟨ [ ℓ ↦' ε ] ε₁ × [ ℓ ↦' ε ] ε₂ ⟩
×-↦'-distr {k = k} ℓ ε = act-×-commutes (replace-at (ctx-idx k) (weaken-ε-k _ ε))

≡̂-↦'-distr : ∀ ℓ (ε : CExpr ℓ) (ε₁ ε₂ τ : CExpr (suc k + ℓ))
           → [ ℓ ↦' ε ] (ε₁ ≡̂ ε₂ of τ) ≡ ([ ℓ ↦' ε ] ε₁) ≡̂ ([ ℓ ↦' ε ] ε₂) of ([ ℓ ↦' ε ] τ)
≡̂-↦'-distr {k = k} ℓ ε = act-≡̂-commutes (replace-at (ctx-idx k) (weaken-ε-k _ ε))

Σ-↦'-distr : ∀ ℓ (ε : CExpr ℓ) (τ ε₀ : CExpr (suc k + ℓ))
           → [ ℓ ↦' ε ] Σ[ τ ] ε₀ ≡ Σ[ [ ℓ ↦' ε ] τ ] ([ ℓ ↦' ε ] ε₀)
Σ-↦'-distr {k = k} ℓ ε = act-Σ-commutes (replace-at (ctx-idx k) (weaken-ε-k _ ε))
