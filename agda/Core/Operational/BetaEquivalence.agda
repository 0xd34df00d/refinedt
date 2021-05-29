{-# OPTIONS --safe #-}

module Core.Operational.BetaEquivalence where

open import Data.Fin using (zero)

open import Core.Syntax
open import Core.Syntax.Substitution
open import Core.Operational

infix 4 _↝β_
data _↝β_ : CExpr ℓ → CExpr ℓ → Set where
  ↝βτ-Subst : ∀ ι ε ε' (ε₀ : CExpr (suc ℓ))
            → (ε↝ε' : ε ↝ ε')
            → [ ι ↦ ε' ] ε₀ ↝β [ ι ↦ ε ] ε₀

infix 4 _↭β_
data _↭β_ : CExpr ℓ → CExpr ℓ → Set where
  forward : (ε₁↝ε₂ : ε₁ ↝β ε₂)
          → ε₁ ↭β ε₂
  backward : (ε₂↝ε₁ : ε₂ ↝β ε₁)
           → ε₁ ↭β ε₂

↝-as-↭β : ε ↝ ε'
        → ε ↭β ε'
↝-as-↭β ε↝ε' = backward (↝βτ-Subst zero _ _ (CVar zero) ε↝ε')

↜-as-↭β : ε ↝ ε'
        → ε' ↭β ε
↜-as-↭β ε↝ε' = forward (↝βτ-Subst zero _ _ (CVar zero) ε↝ε')
