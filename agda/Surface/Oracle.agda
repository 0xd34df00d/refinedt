{-# OPTIONS --safe #-}

module Surface.Oracle where

open import Data.Maybe using (Maybe)

open import Surface.WellScoped

record PositiveDecision : Set where
  constructor MkPD

record Oracle : Set where
  constructor MkOracle
  field
    decide : (Γ : Ctx ℓ) → (b : BaseType) → (ρ₁ ρ₂ : Refinement (suc ℓ)) → Maybe PositiveDecision
