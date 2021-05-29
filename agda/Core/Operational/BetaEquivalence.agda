{-# OPTIONS --safe #-}

module Core.Operational.BetaEquivalence where

open import Core.Syntax
open import Core.Syntax.Substitution
open import Core.Operational

infix 5 _↝β_
data _↝β_ : CExpr ℓ → CExpr ℓ → Set where
  ↝βτ-Subst : ∀ ι ε ε' (ε₀ : CExpr (suc ℓ))
            → (ε↝ε' : ε ↝ ε')
            → [ ι ↦ ε' ] ε₀ ↝β [ ι ↦ ε ] ε₀

infix 5 _↭β_
data _↭β_ : CExpr ℓ → CExpr ℓ → Set where
  forward : (ε₁↝ε₂ : ε₁ ↝β ε₂)
          → ε₁ ↭β ε₂
  backward : (ε₂↝ε₁ : ε₂ ↝β ε₁)
           → ε₁ ↭β ε₂
