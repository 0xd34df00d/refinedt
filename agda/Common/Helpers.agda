{-# OPTIONS --safe #-}

module Common.Helpers where

open import Data.Nat.Base using (ℕ; suc; zero; _+_)
open import Data.Fin.Base using (Fin; suc; zero)
open import Data.Fin.Properties using (suc-injective)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Types
open import Data.Fin.Extra

infix 2 _f≡_
_f≡_ : ∀ {A B : Set} (f₁ f₂ : A → B) → Set
f₁ f≡ f₂ = ∀ x → f₁ x ≡ f₂ x

replace-at-generic : {TermTy : ℕ → Set}
                   → (MkVar : ∀ {ℓ} → Fin ℓ → TermTy ℓ)
                   → ∀ {ℓ} → Fin (suc ℓ) → TermTy ℓ → Fin (suc ℓ) → TermTy ℓ
replace-at-generic MkVar replace-idx ε var-idx with replace-idx <>? var-idx
-- replacement index is less than current variable index, so the variable points to a binder that just got closer to it,
-- so decrement the variable index:
... | less rep<var = MkVar (m<n-n-pred rep<var)
-- just replace the current variable with the term:
... | equal m≡n = ε
-- replacement index is greater than current variable index, so the variable still refers to the same binder,
-- so leave the var index as-is, just shrinking the bound of Fin as the binders count just decremented:
... | greater rep>var = MkVar (tighten rep>var)

ext-ρ : ∀ {ℓ ℓ'}
      → (Fin ℓ → Fin ℓ')
      → Fin (suc ℓ) → Fin (suc ℓ')
ext-ρ ρ zero = zero
ext-ρ ρ (suc ι) = suc (ρ ι)

ext-distr : ∀ {ℓ₀ ℓ₁ ℓ₂}
          → (ρ₁ : Fin ℓ₀ → Fin ℓ₁)
          → (ρ₂ : Fin ℓ₁ → Fin ℓ₂)
          → ext-ρ ρ₂ ∘ ext-ρ ρ₁ f≡ ext-ρ (ρ₂ ∘ ρ₁)
ext-distr _ _ zero = refl
ext-distr _ _ (suc x) = refl

ext-inj : {f : Fin ℓ → Fin ℓ'}
        → Injective f
        → Injective (ext-ρ f)
ext-inj f-inj {zero} {zero} ext-≡ = refl
ext-inj f-inj {suc x₁} {suc x₂} ext-≡ rewrite f-inj (suc-injective ext-≡) = refl

-- This has a slightly different (and less generic) type
-- than the ext-k version from the Actions modules,
-- so it normalizes slightly differently
-- and is more convenient in the context of this module.
ext-k' : ∀ {ℓ}
       → (k : ℕ)
       → (ρ : Fin ℓ → Fin (suc ℓ))
       → Fin (k + ℓ) → Fin (suc k + ℓ)
ext-k' zero ρ = ρ
ext-k' (suc k) ρ = ext-ρ (ext-k' k ρ)

ext-k'-inj : {f : Fin ℓ → Fin (suc ℓ)}
           → ∀ k
           → Injective f
           → Injective (ext-k' k f)
ext-k'-inj zero f-inj = f-inj
ext-k'-inj (suc k) f-inj = ext-inj (ext-k'-inj k f-inj)

ctx-idx : ∀ {ℓ} k → Fin (suc (k + ℓ))
ctx-idx zero = zero
ctx-idx (suc k) = suc (ctx-idx k)
