{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Agreement.Lemmas where

open import Surface.Syntax
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Agreement.Γok
open import Surface.Derivations.Algorithmic.Theorems.Helpers

Γ,τ₁⊢τ₂-⇒-Γ⊢τ₁⇒τ₂ : Γ , τ₁ ⊢[ θ , φ ] τ₂
                  → Γ ⊢[ θ , φ ] τ₁ ⇒ τ₂
Γ,τ₁⊢τ₂-⇒-Γ⊢τ₁⇒τ₂ τ₂δ = TWF-Arr (Γok-head (Γ⊢τ-⇒-Γok τ₂δ)) τ₂δ
