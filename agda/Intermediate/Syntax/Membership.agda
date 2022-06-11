{-# OPTIONS --safe #-}

module Intermediate.Syntax.Membership where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Intermediate.Syntax
open import Intermediate.Syntax.Renaming as R

infix 4 _∈_at_
data _∈_at_ : IType ℓ → Ctx ℓ → Fin ℓ → Set where
  ∈-zero : (≡-prf : τ₀ ≡ R.weaken-τ τ)
         → τ₀ ∈ Γ , τ at zero
  ∈-suc  : (≡-prf : τ₀ ≡ R.weaken-τ τ)
         → (there : τ ∈ Γ at ι)
         → τ₀ ∈ Γ , τ' at suc ι

∈-injective : τ₁ ∈ Γ at ι
            → τ₂ ∈ Γ at ι
            → τ₁ ≡ τ₂
∈-injective (∈-zero refl) (∈-zero refl) = refl
∈-injective (∈-suc refl ∈₁) (∈-suc refl ∈₂) rewrite ∈-injective ∈₁ ∈₂ = refl

infix 4 _ℕ-idx_∈_
data _ℕ-idx_∈_ : (k : ℕ) → IType ℓ → Ctx (suc k + ℓ) → Set where
  ∈-zero : zero ℕ-idx τ ∈ (Γ , τ)
  ∈-suc  : ∀ {Γ : Ctx (suc k + ℓ)} {τ' : IType (suc k + ℓ)}
         → k ℕ-idx τ ∈ Γ
         → suc k ℕ-idx τ ∈ (Γ , τ')
