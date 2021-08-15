{-# OPTIONS --safe #-}

module Surface.Operational.BetaEquivalence where

open import Data.Fin using (zero; suc)
open import Data.Vec.Base using (lookup; [_]; _∷_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Data.Fin.Extra
open import Surface.Syntax
open import Surface.Syntax.Renaming as R
open import Surface.Syntax.Substitution as S
open import Surface.Syntax.Substitution.Commutativity
open import Surface.Syntax.Substitution.Distributivity
open import Surface.Syntax.Shape
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

infix 5 _↭βτ⋆_
data _↭βτ⋆_ : SType ℓ → SType ℓ → Set where
  ↝-refl  : τ ↭βτ⋆ τ
  ↝-trans : τ₁ ↭βτ τ₂
          → τ₂ ↭βτ⋆ τ₃
          → τ₁ ↭βτ⋆ τ₃

↭βτ-is-symmetric : τ₁ ↭βτ τ₂
                 → τ₂ ↭βτ τ₁
↭βτ-is-symmetric (forward τ₁↝τ₂) = backward τ₁↝τ₂
↭βτ-is-symmetric (backward τ₂↝τ₁) = forward τ₂↝τ₁

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

↭-via-↝ : {f : SType ℓ → SType ℓ'}
        → f preserves _↝βτ_
        → f preserves _↭βτ_
↭-via-↝ f-↝βτ (forward  τ₁↝τ₂) = forward  (f-↝βτ τ₁↝τ₂)
↭-via-↝ f-↝βτ (backward τ₂↝τ₁) = backward (f-↝βτ τ₂↝τ₁)

ρ-preserves-↭βτ : (ρ : Fin ℓ → Fin ℓ')
                → R.act-τ ρ preserves _↭βτ_
ρ-preserves-↭βτ = ↭-via-↝ ∘ ρ-preserves-↝βτ

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

↦τ-preserves-↭βτ : ∀ ι (ε₀ : STerm ℓ)
                 → [ ι ↦τ ε₀ ]_ preserves _↭βτ_
↦τ-preserves-↭βτ ι ε₀ = ↭-via-↝ (↦τ-preserves-↝βτ ι ε₀)

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

prove-via-↝βτ' : (τ₁ ↝βτ' τ₂ → τ₁' ↝βτ' τ₂')
               → (τ₁ ↝βτ  τ₂ → τ₁' ↝βτ  τ₂')
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

↭βτ-preserves-shape : ShapePreserving {ℓ} _↭βτ_
↭βτ-preserves-shape (forward τ₁↝τ₂) = ↝βτ-preserves-shape τ₁↝τ₂
↭βτ-preserves-shape (backward τ₂↝τ₁) = sym (↝βτ-preserves-shape τ₂↝τ₁)

↝βτ'-cons-same-length : ∀ {n₁ n₂}
                      → {cons₁ : ADTCons (Mkℕₐ n₁) ℓ}
                      → {cons₂ : ADTCons (Mkℕₐ n₂) ℓ}
                      → (⊍ cons₁) ↝βτ' (⊍ cons₂)
                      → n₁ ≡ n₂
↝βτ'-cons-same-length (↝βτ'-Subst _ _ _ (⊍ cons) _ refl refl) = refl

↝βτ-cons-same-length : ∀ {n₁ n₂}
                     → {cons₁ : ADTCons (Mkℕₐ n₁) ℓ}
                     → {cons₂ : ADTCons (Mkℕₐ n₂) ℓ}
                     → (⊍ cons₁) ↝βτ (⊍ cons₂)
                     → n₁ ≡ n₂
↝βτ-cons-same-length ↝βτ = ↝βτ'-cons-same-length (↝βτ-to-↝βτ' ↝βτ)

↭βτ-cons-same-length : ∀ {n₁ n₂}
                     → {cons₁ : ADTCons (Mkℕₐ n₁) ℓ}
                     → {cons₂ : ADTCons (Mkℕₐ n₂) ℓ}
                     → (⊍ cons₁) ↭βτ (⊍ cons₂)
                     → n₁ ≡ n₂
↭βτ-cons-same-length (forward τ₁↝τ₂) = ↝βτ-cons-same-length τ₁↝τ₂
↭βτ-cons-same-length (backward τ₂↝τ₁) = sym (↝βτ-cons-same-length τ₂↝τ₁)

↝βτ'-lookup : (ι : Fin n)
            → (cons₁ : ADTCons (Mkℕₐ n) ℓ)
            → (cons₂ : ADTCons (Mkℕₐ n) ℓ)
            → (⊍ cons₁) ↝βτ' (⊍ cons₂)
            → lookup cons₁ ι ↝βτ' lookup cons₂ ι
↝βτ'-lookup             zero    (x₁ ∷ _)    (x₂ ∷ _)    (↝βτ'-Subst ι' ε ε' (⊍ (x ∷ _)) ε↝ε' refl refl) = ↝βτ'-Subst ι' ε ε' x ε↝ε' refl refl
↝βτ'-lookup {n = suc n} (suc ι) (_ ∷ cons₁) (_ ∷ cons₂) (↝βτ'-Subst ι' ε ε' (⊍ (_ ∷ cons)) ε↝ε' refl refl)
  = ↝βτ'-lookup ι cons₁ cons₂ (↝βτ'-Subst ι' ε ε' (⊍ cons) ε↝ε' refl refl)

↝βτ-lookup : {cons₁ : ADTCons (Mkℕₐ n) ℓ}
           → {cons₂ : ADTCons (Mkℕₐ n) ℓ}
           → (ι : Fin n)
           → (⊍ cons₁) ↝βτ (⊍ cons₂)
           → lookup cons₁ ι ↝βτ lookup cons₂ ι
↝βτ-lookup ι = prove-via-↝βτ' (↝βτ'-lookup ι _ _)

↭βτ-lookup : {cons₁ : ADTCons (Mkℕₐ n) ℓ}
           → {cons₂ : ADTCons (Mkℕₐ n) ℓ}
           → (ι : Fin n)
           → (⊍ cons₁) ↭βτ (⊍ cons₂)
           → lookup cons₁ ι ↭βτ lookup cons₂ ι
↭βτ-lookup ι (forward τ₁↝τ₂) = forward (↝βτ-lookup ι τ₁↝τ₂)
↭βτ-lookup ι (backward τ₂↝τ₁) = backward (↝βτ-lookup ι τ₂↝τ₁)

↝βτ'-⇒-dom : (τ₁ ⇒ τ₂) ↝βτ' (τ₁' ⇒ τ₂')
           → τ₁ ↝βτ' τ₁'
↝βτ'-⇒-dom (↝βτ'-Subst ι ε ε' (τ₀₁ ⇒ τ₀₂) ε↝ε' refl refl) = ↝βτ'-Subst ι ε ε' τ₀₁ ε↝ε' refl refl

↝βτ'-⇒-cod : (τ₁ ⇒ τ₂) ↝βτ' (τ₁' ⇒ τ₂')
           → τ₂ ↝βτ' τ₂'
↝βτ'-⇒-cod (↝βτ'-Subst ι ε ε' (τ₀₁ ⇒ τ₀₂) ε↝ε' refl refl)
  rewrite S.act-τ-extensionality (ext-replace-comm ε' ι) τ₀₂
        | S.act-τ-extensionality (ext-replace-comm ε  ι) τ₀₂
        = ↝βτ'-Subst (suc ι) (R.weaken-ε ε) (R.weaken-ε ε') τ₀₂ (ρ-preserves-↝ suc ε↝ε') refl refl

↝βτ-⇒-dom : (τ₁ ⇒ τ₂) ↝βτ (τ₁' ⇒ τ₂')
          → τ₁ ↝βτ τ₁'
↝βτ-⇒-dom = prove-via-↝βτ' ↝βτ'-⇒-dom

↝βτ-⇒-cod : (τ₁ ⇒ τ₂) ↝βτ (τ₁' ⇒ τ₂')
          → τ₂ ↝βτ τ₂'
↝βτ-⇒-cod = prove-via-↝βτ' ↝βτ'-⇒-cod

↭βτ-⇒-dom : (τ₁ ⇒ τ₂) ↭βτ (τ₁' ⇒ τ₂')
          → τ₁ ↭βτ τ₁'
↭βτ-⇒-dom (forward ⇒₁↝⇒₂) = forward (↝βτ-⇒-dom ⇒₁↝⇒₂)
↭βτ-⇒-dom (backward ⇒₂↝⇒₁) = backward (↝βτ-⇒-dom ⇒₂↝⇒₁)

↭βτ-⇒-cod : (τ₁ ⇒ τ₂) ↭βτ (τ₁' ⇒ τ₂')
          → τ₂ ↭βτ τ₂'
↭βτ-⇒-cod (forward ⇒₁↝⇒₂) = forward (↝βτ-⇒-cod ⇒₁↝⇒₂)
↭βτ-⇒-cod (backward ⇒₂↝⇒₁) = backward (↝βτ-⇒-cod ⇒₂↝⇒₁)
