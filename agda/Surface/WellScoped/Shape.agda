{-# OPTIONS --safe #-}

module Surface.WellScoped.Shape where

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Surface.WellScoped

data Shape : Set where
  Sh-⟨∣⟩ : Shape
  Sh-⇒   : Shape
  Sh-⊍   : Shape

shape-of : SType ℓ → Shape
shape-of ⟨ _ ∣ _ ⟩ = Sh-⟨∣⟩
shape-of (_ ⇒ _) = Sh-⇒
shape-of (⊍ _) = Sh-⊍

ShapePreserving : (SType ℓ₁ → SType ℓ₂ → Set) → Set
ShapePreserving _rel_ = ∀ {τ₁ τ₂}
                        → τ₁ rel τ₂
                        → shape-of τ₁ ≡ shape-of τ₂

shape-⊥-elim : {A : Set}
             → {_rel_ : SType ℓ₁ → SType ℓ₂ → Set}
             → ShapePreserving _rel_
             → τ₁ rel τ₂
             → ¬ (shape-of τ₁ ≡ shape-of τ₂)
             → A
shape-⊥-elim pres rel neq = ⊥-elim (neq (pres rel))
