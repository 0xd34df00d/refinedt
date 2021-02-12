{-# OPTIONS --safe #-}

module Common.Types where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

record ℕₐ : Set where
  constructor Mkℕₐ
  field
    get-length : ℕ

variable
  nₐ : ℕₐ

Injective : {A B : Set} → (A → B) → Set
Injective f = ∀ {x₁ x₂}
              → f x₁ ≡ f x₂
              → x₁ ≡ x₂
