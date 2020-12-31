{-# OPTIONS --safe #-}

module Surface.Operational.BetaEquivalence where

open import Data.Fin using (zero; suc)
open import Data.Vec.Base using (lookup; [_]; _∷_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Fin.Extra
open import Surface.WellScoped
open import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.Substitution as S
open import Surface.WellScoped.Substitution.Commutativity
open import Surface.WellScoped.Substitution.Distributivity
open import Surface.WellScoped.Shape
open import Surface.Operational
open import Surface.Operational.Lemmas

infix 5 _≡rβ_
data _≡rβ_ : SType ℓ → SType ℓ → Set where
  ≡rβ-Subst : ∀ ε ε' (τ : SType (suc ℓ))
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
subst-preserves-↝ ι ε₀ (E-CaseMatch {ϖ = ϖ} {bs = bs} is-value idx)
  rewrite σ-↦ₘ-comm (replace-at ι ε₀) idx ϖ bs
        = E-CaseMatch (σ-preserves-values is-value) idx

↦τ-preserves-≡rβ : ∀ ι ε₀
                 → τ₁ ≡rβ τ₂
                 → ([ ι ↦τ ε₀ ] τ₁) ≡rβ ([ ι ↦τ ε₀ ] τ₂)
↦τ-preserves-≡rβ ι ε₀ (≡rβ-Subst ε ε' τ ε↝ε')
  rewrite subst-commutes-τ ι ε₀ ε' τ
        | subst-commutes-τ ι ε₀ ε  τ
        = ≡rβ-Subst _ _ ([ suc ι ↦τ weaken-ε ε₀ ] τ) (subst-preserves-↝ ι ε₀ ε↝ε')

-- The version of the restricted β-equivalence without the green slime, more useful in proofs
infix 5 _≡rβ'_
data _≡rβ'_ : SType ℓ → SType ℓ → Set where
  ≡rβ'-Subst : ∀ ε ε' (τ : SType (suc ℓ))
             → (ε↝ε' : ε ↝ ε')
             → (τ₁-≡ : τ₁ ≡ [ zero ↦τ ε' ] τ)
             → (τ₂-≡ : τ₂ ≡ [ zero ↦τ ε  ] τ)
             → τ₁ ≡rβ' τ₂

≡rβ-to-≡rβ' : τ₁ ≡rβ  τ₂
            → τ₁ ≡rβ' τ₂
≡rβ-to-≡rβ' (≡rβ-Subst ε ε' τ ε↝ε') = ≡rβ'-Subst ε ε' τ ε↝ε' refl refl

≡rβ'-to-≡rβ : τ₁ ≡rβ' τ₂
            → τ₁ ≡rβ  τ₂
≡rβ'-to-≡rβ (≡rβ'-Subst ε ε' τ ε↝ε' refl refl) = ≡rβ-Subst ε ε' τ ε↝ε'

≡rβ-⇔-≡rβ' : (τ₁ ≡rβ' τ₂ → τ₁' ≡rβ'  τ₂')
           → (τ₁ ≡rβ  τ₂ → τ₁' ≡rβ   τ₂')
≡rβ-⇔-≡rβ' f = ≡rβ'-to-≡rβ ∘ f ∘ ≡rβ-to-≡rβ'


≡rβ'-preserves-shape : ShapePreserving {ℓ} _≡rβ'_
≡rβ'-preserves-shape {τ₁ = ⟨ _ ∣ _ ⟩} {τ₂ = ⟨ _ ∣ _ ⟩} _ = refl
≡rβ'-preserves-shape {τ₁ = _ ⇒ _} {τ₂ = _ ⇒ _} _ = refl
≡rβ'-preserves-shape {τ₁ = ⊍ _} {τ₂ = ⊍ _} _ = refl
≡rβ'-preserves-shape {τ₁ = ⟨ _ ∣ _ ⟩} {τ₂ = τ₂ ⇒ τ₃} (≡rβ'-Subst ε ε' τ ε↝ε' τ₁-≡ τ₂-≡)
  = shape-contra₂ (↦τ-preserves-shape zero ε') (↦τ-preserves-shape zero ε) τ₁-≡ τ₂-≡ λ ()
≡rβ'-preserves-shape {τ₁ = ⟨ _ ∣ _ ⟩} {τ₂ = ⊍ _} (≡rβ'-Subst ε ε' τ ε↝ε' τ₁-≡ τ₂-≡)
  = shape-contra₂ (↦τ-preserves-shape zero ε') (↦τ-preserves-shape zero ε) τ₁-≡ τ₂-≡ λ ()
≡rβ'-preserves-shape {τ₁ = _ ⇒ _} {τ₂ = ⟨ _ ∣ _ ⟩} (≡rβ'-Subst ε ε' τ ε↝ε' τ₁-≡ τ₂-≡)
  = shape-contra₂ (↦τ-preserves-shape zero ε') (↦τ-preserves-shape zero ε) τ₁-≡ τ₂-≡ λ ()
≡rβ'-preserves-shape {τ₁ = _ ⇒ _} {τ₂ = ⊍ _} (≡rβ'-Subst ε ε' τ ε↝ε' τ₁-≡ τ₂-≡)
  = shape-contra₂ (↦τ-preserves-shape zero ε') (↦τ-preserves-shape zero ε) τ₁-≡ τ₂-≡ λ ()
≡rβ'-preserves-shape {τ₁ = ⊍ _} {τ₂ = ⟨ _ ∣ _ ⟩} (≡rβ'-Subst ε ε' τ ε↝ε' τ₁-≡ τ₂-≡)
  = shape-contra₂ (↦τ-preserves-shape zero ε') (↦τ-preserves-shape zero ε) τ₁-≡ τ₂-≡ λ ()
≡rβ'-preserves-shape {τ₁ = ⊍ _} {τ₂ = _ ⇒ _} (≡rβ'-Subst ε ε' τ ε↝ε' τ₁-≡ τ₂-≡)
  = shape-contra₂ (↦τ-preserves-shape zero ε') (↦τ-preserves-shape zero ε) τ₁-≡ τ₂-≡ λ ()

≡rβ-preserves-shape : ShapePreserving {ℓ} _≡rβ_
≡rβ-preserves-shape ≡rβ = ≡rβ'-preserves-shape (≡rβ-to-≡rβ' ≡rβ)


≡rβ'-cons-same-length : ∀ {n₁ n₂}
                      → {cons₁ : ADTCons (Mkℕₐ (suc n₁)) ℓ}
                      → {cons₂ : ADTCons (Mkℕₐ (suc n₂)) ℓ}
                      → (⊍ cons₁) ≡rβ' (⊍ cons₂)
                      → n₁ ≡ n₂
≡rβ'-cons-same-length (≡rβ'-Subst _ _ (⊍ cons) _ refl refl) = refl

≡rβ-cons-same-length : ∀ {n₁ n₂}
                     → {cons₁ : ADTCons (Mkℕₐ (suc n₁)) ℓ}
                     → {cons₂ : ADTCons (Mkℕₐ (suc n₂)) ℓ}
                     → (⊍ cons₁) ≡rβ (⊍ cons₂)
                     → n₁ ≡ n₂
≡rβ-cons-same-length ≡rβ = ≡rβ'-cons-same-length (≡rβ-to-≡rβ' ≡rβ)

≡rβ'-lookup : (idx : Fin (suc n))
            → (cons₁ : ADTCons (Mkℕₐ (suc n)) ℓ)
            → (cons₂ : ADTCons (Mkℕₐ (suc n)) ℓ)
            → (⊍ cons₁) ≡rβ' (⊍ cons₂)
            → lookup cons₁ idx ≡rβ' lookup cons₂ idx
≡rβ'-lookup             zero      (x₁ ∷ _)    (x₂ ∷ _)    (≡rβ'-Subst ε ε' (⊍ (x ∷ _)) ε↝ε' refl refl) = ≡rβ'-Subst ε ε' x ε↝ε' refl refl
≡rβ'-lookup {n = suc n} (suc idx) (_ ∷ cons₁) (_ ∷ cons₂) (≡rβ'-Subst ε ε' (⊍ (_ ∷ cons)) ε↝ε' refl refl)
  = ≡rβ'-lookup idx cons₁ cons₂ (≡rβ'-Subst ε ε' (⊍ cons) ε↝ε' refl refl)

≡rβ-lookup : {cons₁ : ADTCons (Mkℕₐ (suc n)) ℓ}
           → {cons₂ : ADTCons (Mkℕₐ (suc n)) ℓ}
           → (idx : Fin (suc n))
           → (⊍ cons₁) ≡rβ (⊍ cons₂)
           → lookup cons₁ idx ≡rβ lookup cons₂ idx
≡rβ-lookup idx = ≡rβ-⇔-≡rβ' (≡rβ'-lookup idx _ _)
