{-# OPTIONS --safe #-}

module Common.Inequalities where

open import Data.Nat
open import Data.Nat.Properties

a<1+[a⊔b]⊔c : ∀ a b c
            → a ≤ suc (a ⊔ b) ⊔ c
a<1+[a⊔b]⊔c a b c = ≤-trans (m≤m⊔n a b) (≤-trans (≤-step ≤-refl) (m≤m⊔n _ c))
