{-# OPTIONS --safe #-}

module Common.Helpers where

open import Relation.Binary.PropositionalEquality using (_≡_)

infix 2 _f≡_
_f≡_ : ∀ {A B : Set} (f₁ f₂ : A → B) → Set
f₁ f≡ f₂ = ∀ x → f₁ x ≡ f₂ x
