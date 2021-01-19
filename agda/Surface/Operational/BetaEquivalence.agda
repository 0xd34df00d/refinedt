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

infix 5 _↝βτ_
data _↝βτ_ : SType ℓ → SType ℓ → Set where
  ↝βτ-Subst : ∀ ι ε ε' (τ : SType (suc ℓ))
            → (ε↝ε' : ε ↝ ε')
            → [ ι ↦τ ε' ] τ ↝βτ [ ι ↦τ ε ] τ

infix 5 _↭βτ_
data _↭βτ_ : SType ℓ → SType ℓ → Set where
  forward : (τ₁↝τ₂ : τ₁ ↝βτ τ₂)
          → τ₁ ↭βτ τ₂
  backward : (τ₂↝τ₁ : τ₂ ↝βτ τ₁)
           → τ₁ ↭βτ τ₂

_preserves_ : (SType ℓ → SType ℓ')
            → (∀ {ℓ} → SType ℓ → SType ℓ → Set)
            → Set
f preserves _R_ = ∀ {τ₁ τ₂}
                → τ₁ R τ₂
                → f τ₁ R f τ₂

ρ-preserves-↝βτ : (ρ : Fin ℓ → Fin ℓ')
                → R.act-τ ρ preserves _↝βτ_
ρ-preserves-↝βτ ρ (↝βτ-Subst ι ε ε' τ ε↝ε')
  rewrite ρ-subst-distr-τ ρ ι ε  τ
        | ρ-subst-distr-τ ρ ι ε' τ
        = ↝βτ-Subst zero (R.act-ε ρ ε) (R.act-ε ρ ε') (R.act-τ (ρ-ιth ρ ι) τ) (ρ-preserves-↝ ρ ε↝ε')

↦τ-preserves-↝βτ : ∀ ι (ε₀ : STerm ℓ)
                 → [ ι ↦τ ε₀ ]_ preserves _↝βτ_
↦τ-preserves-↝βτ ι ε₀ (↝βτ-Subst ιₛ ε ε' τ ε↝ε')
  rewrite subst-commutes-τ ι ιₛ ε₀ ε' τ
        | subst-commutes-τ ι ιₛ ε₀ ε  τ
        = ↝βτ-Subst
              (compute-ι'₂ ι ιₛ)
              ([ ι ↦ε ε₀ ] ε)
              ([ ι ↦ε ε₀ ] ε')
              ([ compute-ι'₁ ι ιₛ ↦τ R.act-ε (make-room-for (compute-ι'₂ ι ιₛ)) ε₀ ] τ)
              (subst-preserves-↝ ι ε₀ ε↝ε')

-- The version of the restricted β-equivalence without the green slime, more useful in proofs
infix 5 _↝βτ'_
data _↝βτ'_ : SType ℓ → SType ℓ → Set where
  ↝βτ'-Subst : ∀ ι ε ε' (τ : SType (suc ℓ))
             → (ε↝ε' : ε ↝ ε')
             → (τ₁-≡ : τ₁ ≡ [ ι ↦τ ε' ] τ)
             → (τ₂-≡ : τ₂ ≡ [ ι ↦τ ε  ] τ)
             → τ₁ ↝βτ' τ₂

↝βτ-to-↝βτ' : τ₁ ↝βτ  τ₂
            → τ₁ ↝βτ' τ₂
↝βτ-to-↝βτ' (↝βτ-Subst ι ε ε' τ ε↝ε') = ↝βτ'-Subst ι ε ε' τ ε↝ε' refl refl

↝βτ'-to-↝βτ : τ₁ ↝βτ' τ₂
            → τ₁ ↝βτ  τ₂
↝βτ'-to-↝βτ (↝βτ'-Subst ι ε ε' τ ε↝ε' refl refl) = ↝βτ-Subst ι ε ε' τ ε↝ε'

prove-via-↝βτ' : (τ₁ ↝βτ' τ₂ → τ₁' ↝βτ'  τ₂')
               → (τ₁ ↝βτ  τ₂ → τ₁' ↝βτ   τ₂')
prove-via-↝βτ' f = ↝βτ'-to-↝βτ ∘ f ∘ ↝βτ-to-↝βτ'


↝βτ'-preserves-shape : ShapePreserving {ℓ} _↝βτ'_
↝βτ'-preserves-shape {τ₁ = ⟨ _ ∣ _ ⟩} {τ₂ = ⟨ _ ∣ _ ⟩} _ = refl
↝βτ'-preserves-shape {τ₁ = _ ⇒ _} {τ₂ = _ ⇒ _} _ = refl
↝βτ'-preserves-shape {τ₁ = ⊍ _} {τ₂ = ⊍ _} _ = refl
↝βτ'-preserves-shape {τ₁ = ⟨ _ ∣ _ ⟩} {τ₂ = τ₂ ⇒ τ₃} (↝βτ'-Subst ι ε ε' τ ε↝ε' τ₁-≡ τ₂-≡)
  = shape-contra₂ (↦τ-preserves-shape ι ε') (↦τ-preserves-shape ι ε) τ₁-≡ τ₂-≡ λ ()
↝βτ'-preserves-shape {τ₁ = ⟨ _ ∣ _ ⟩} {τ₂ = ⊍ _} (↝βτ'-Subst ι ε ε' τ ε↝ε' τ₁-≡ τ₂-≡)
  = shape-contra₂ (↦τ-preserves-shape ι ε') (↦τ-preserves-shape ι ε) τ₁-≡ τ₂-≡ λ ()
↝βτ'-preserves-shape {τ₁ = _ ⇒ _} {τ₂ = ⟨ _ ∣ _ ⟩} (↝βτ'-Subst ι ε ε' τ ε↝ε' τ₁-≡ τ₂-≡)
  = shape-contra₂ (↦τ-preserves-shape ι ε') (↦τ-preserves-shape ι ε) τ₁-≡ τ₂-≡ λ ()
↝βτ'-preserves-shape {τ₁ = _ ⇒ _} {τ₂ = ⊍ _} (↝βτ'-Subst ι ε ε' τ ε↝ε' τ₁-≡ τ₂-≡)
  = shape-contra₂ (↦τ-preserves-shape ι ε') (↦τ-preserves-shape ι ε) τ₁-≡ τ₂-≡ λ ()
↝βτ'-preserves-shape {τ₁ = ⊍ _} {τ₂ = ⟨ _ ∣ _ ⟩} (↝βτ'-Subst ι ε ε' τ ε↝ε' τ₁-≡ τ₂-≡)
  = shape-contra₂ (↦τ-preserves-shape ι ε') (↦τ-preserves-shape ι ε) τ₁-≡ τ₂-≡ λ ()
↝βτ'-preserves-shape {τ₁ = ⊍ _} {τ₂ = _ ⇒ _} (↝βτ'-Subst ι ε ε' τ ε↝ε' τ₁-≡ τ₂-≡)
  = shape-contra₂ (↦τ-preserves-shape ι ε') (↦τ-preserves-shape ι ε) τ₁-≡ τ₂-≡ λ ()

↝βτ-preserves-shape : ShapePreserving {ℓ} _↝βτ_
↝βτ-preserves-shape ↝βτ = ↝βτ'-preserves-shape (↝βτ-to-↝βτ' ↝βτ)


↝βτ'-cons-same-length : ∀ {n₁ n₂}
                      → {cons₁ : ADTCons (Mkℕₐ (suc n₁)) ℓ}
                      → {cons₂ : ADTCons (Mkℕₐ (suc n₂)) ℓ}
                      → (⊍ cons₁) ↝βτ' (⊍ cons₂)
                      → n₁ ≡ n₂
↝βτ'-cons-same-length (↝βτ'-Subst _ _ _ (⊍ cons) _ refl refl) = refl

↝βτ-cons-same-length : ∀ {n₁ n₂}
                     → {cons₁ : ADTCons (Mkℕₐ (suc n₁)) ℓ}
                     → {cons₂ : ADTCons (Mkℕₐ (suc n₂)) ℓ}
                     → (⊍ cons₁) ↝βτ (⊍ cons₂)
                     → n₁ ≡ n₂
↝βτ-cons-same-length ↝βτ = ↝βτ'-cons-same-length (↝βτ-to-↝βτ' ↝βτ)

↝βτ'-lookup : (idx : Fin (suc n))
            → (cons₁ : ADTCons (Mkℕₐ (suc n)) ℓ)
            → (cons₂ : ADTCons (Mkℕₐ (suc n)) ℓ)
            → (⊍ cons₁) ↝βτ' (⊍ cons₂)
            → lookup cons₁ idx ↝βτ' lookup cons₂ idx
↝βτ'-lookup             zero      (x₁ ∷ _)    (x₂ ∷ _)    (↝βτ'-Subst ι ε ε' (⊍ (x ∷ _)) ε↝ε' refl refl) = ↝βτ'-Subst ι ε ε' x ε↝ε' refl refl
↝βτ'-lookup {n = suc n} (suc idx) (_ ∷ cons₁) (_ ∷ cons₂) (↝βτ'-Subst ι ε ε' (⊍ (_ ∷ cons)) ε↝ε' refl refl)
  = ↝βτ'-lookup idx cons₁ cons₂ (↝βτ'-Subst ι ε ε' (⊍ cons) ε↝ε' refl refl)

↝βτ-lookup : {cons₁ : ADTCons (Mkℕₐ (suc n)) ℓ}
           → {cons₂ : ADTCons (Mkℕₐ (suc n)) ℓ}
           → (idx : Fin (suc n))
           → (⊍ cons₁) ↝βτ (⊍ cons₂)
           → lookup cons₁ idx ↝βτ lookup cons₂ idx
↝βτ-lookup idx = prove-via-↝βτ' (↝βτ'-lookup idx _ _)

↝βτ'-⇒-dom : (τ₁' ⇒ τ₂') ↝βτ' (τ₁ ⇒ τ₂)
           → τ₁' ↝βτ' τ₁
↝βτ'-⇒-dom (↝βτ'-Subst ι ε ε' (τ₀₁ ⇒ τ₀₂) ε↝ε' refl refl) = ↝βτ'-Subst ι ε ε' τ₀₁ ε↝ε' refl refl

↝βτ'-⇒-cod : (τ₁' ⇒ τ₂') ↝βτ' (τ₁ ⇒ τ₂)
           → τ₂' ↝βτ' τ₂
↝βτ'-⇒-cod (↝βτ'-Subst ι ε ε' (τ₀₁ ⇒ τ₀₂) ε↝ε' refl refl)
  rewrite S.act-τ-extensionality (ext-replace-comm ε' ι) τ₀₂
        | S.act-τ-extensionality (ext-replace-comm ε  ι) τ₀₂
        = ↝βτ'-Subst (suc ι) (R.weaken-ε ε) (R.weaken-ε ε') τ₀₂ (ρ-preserves-↝ suc ε↝ε') refl refl

↝βτ-⇒-dom : (τ₁' ⇒ τ₂') ↝βτ (τ₁ ⇒ τ₂)
          → τ₁' ↝βτ τ₁
↝βτ-⇒-dom = prove-via-↝βτ' ↝βτ'-⇒-dom

↝βτ-⇒-cod : (τ₁' ⇒ τ₂') ↝βτ (τ₁ ⇒ τ₂)
          → τ₂' ↝βτ τ₂
↝βτ-⇒-cod = prove-via-↝βτ' ↝βτ'-⇒-cod
