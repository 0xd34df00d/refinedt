{-# OPTIONS --safe #-}

module Surface.Operational.BetaEquivalence where

open import Data.Fin using (zero)

open import Data.Fin.Extra

open import Surface.WellScoped
open import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.Substitution
open import Surface.WellScoped.Substitution.Distributivity
open import Surface.Operational
open import Surface.Operational.Lemmas

infix 5 _≡rβ_
data _≡rβ_ : SType ℓ → SType ℓ → Set where
  ≡rβ-Subst   : ∀ ε ε' (τ : SType (suc ℓ))
              → (ε↝ε' : ε ↝ ε')
              → [ zero ↦τ ε' ] τ ≡rβ [ zero ↦τ ε ] τ

ρ-preserves-≡rβ : ∀ {ρ : Fin ℓ → Fin ℓ'}
                → Monotonic ρ
                → τ₁ ≡rβ τ₂
                → R.act-τ ρ τ₁ ≡rβ R.act-τ ρ τ₂
ρ-preserves-≡rβ {ρ = ρ} ρ-mono (≡rβ-Subst ε ε' τ ε↝ε')
  rewrite ρ-subst-distr-τ-0 ρ ρ-mono ε τ
        | ρ-subst-distr-τ-0 ρ ρ-mono ε' τ
        = ≡rβ-Subst (R.act-ε ρ ε) (R.act-ε ρ ε') (R.act-τ (R.ext ρ) τ) (ρ-preserves-↝ ρ-mono ε↝ε')
