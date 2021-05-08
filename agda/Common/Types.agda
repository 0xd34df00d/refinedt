{-# OPTIONS --safe #-}

module Common.Types where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)

record ℕₐ : Set where
  constructor Mkℕₐ
  field
    get-length : ℕ

variable
  nₐ : ℕₐ
  k n ℓ ℓ' ℓ₀ ℓ₁ ℓ₂ : ℕ
  idx ι ι₁ ι₂ : Fin ℓ

Injective : {A B : Set} → (A → B) → Set
Injective f = ∀ {x₁ x₂}
              → f x₁ ≡ f x₂
              → x₁ ≡ x₂

Injective₂ : {A B C : Set} → (A → B → C) → Set
Injective₂ f = ∀ {x₁ x₂ x₁' x₂'}
               → f x₁ x₂ ≡ f x₁' x₂'
               → x₁ ≡ x₁' × x₂ ≡ x₂'
