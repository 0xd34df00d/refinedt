{-# OPTIONS --safe #-}

module Core.Syntax.Derived where

open import Core.Syntax
open import Core.Syntax.Renaming

_==>_ : CExpr ℓ → CExpr ℓ → CExpr ℓ
τ₁ ==> τ₂ = CΠ τ₁ (weaken-ε τ₂)

_≡̂_of_ : CExpr ℓ → CExpr ℓ → CExpr ℓ → CExpr ℓ
ε₁ ≡̂ ε₂ of τ = CΠ (τ ==> ⋆ₑ) {! !}
