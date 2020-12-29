{-# OPTIONS --safe #-}

module Surface.Operational.BetaEquivalence where

open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Fin.Extra
open import Surface.WellScoped
open import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.Substitution as S
open import Surface.WellScoped.Substitution.Commutativity
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

subst-preserves-↝ : ∀ ι ε₀
                  → ε ↝ ε'
                  → ([ ι ↦ε ε₀ ] ε) ↝ ([ ι ↦ε ε₀ ] ε')
subst-preserves-↝ ι ε₀ (E-AppL ε↝ε') = E-AppL (subst-preserves-↝ ι ε₀ ε↝ε')
subst-preserves-↝ ι ε₀ (E-AppR is-value ε↝ε') = E-AppR (σ-preserves-values is-value) (subst-preserves-↝ ι ε₀ ε↝ε')
subst-preserves-↝ ι ε₀ (E-AppAbs {ϖ = ϖ} {ε = ε} is-value)
  rewrite subst-commutes-ε ι ε₀ ϖ ε
        | S.act-ε-extensionality (ext-replace-comm ε₀ ι) ε
        = E-AppAbs (σ-preserves-values is-value)
subst-preserves-↝ ι ε₀ (E-ADT ε↝ε') = E-ADT (subst-preserves-↝ ι ε₀ ε↝ε')
subst-preserves-↝ ι ε₀ (E-CaseScrut ε↝ε') = E-CaseScrut (subst-preserves-↝ ι ε₀ ε↝ε')
subst-preserves-↝ ι ε₀ (E-CaseMatch is-value idx) = {! !}

↦τ-preserves-≡rβ : ∀ ι ε₀
                 → τ₁ ≡rβ τ₂
                 → ([ ι ↦τ ε₀ ] τ₁) ≡rβ ([ ι ↦τ ε₀ ] τ₂)
↦τ-preserves-≡rβ ι ε₀ (≡rβ-Subst ε ε' τ ε↝ε')
  rewrite subst-commutes-τ ι ε₀ ε' τ
        | subst-commutes-τ ι ε₀ ε  τ
        = ≡rβ-Subst _ _ ([ suc ι ↦τ weaken-ε ε₀ ] τ) (subst-preserves-↝ ι ε₀ ε↝ε')
