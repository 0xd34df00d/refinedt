{-# OPTIONS --safe #-}

module Surface.Safety where

open import Surface.WellScoped
open import Surface.Derivations
open import Surface.Operational

data Progress (ε : STerm ℓ) : Set where
  step : ∀ ε'
       → (ε↝ε' : ε ↝ ε')
       → Progress ε
  done : (is-value : IsValue ε)
       → Progress ε

progress : ⊘ ⊢ ε ⦂ τ
         → Progress ε
progress (T-Unit Γok) = done IV-Unit
progress (T-Abs arrδ εδ) = done IV-Abs
progress (T-App εδ₁ εδ₂) with progress εδ₁
... | step ε' ε↝ε' = step (SApp ε' _) (E-AppL ε↝ε')
... | done is-value with progress εδ₂
...   | step ε' ε↝ε' = step (SApp _ ε') (E-AppR is-value ε↝ε')
...   | done is-value₁ = {! !}
progress (T-Case resδ εδ branches) with progress εδ
... | step ε' ε↝ε' = step (SCase ε' _) (E-CaseScrut ε↝ε')
... | done is-value = {! !}
progress (T-Con εδ adtτ) = {! !}
progress (T-Sub εδ τδ τ<:τ') = progress εδ
