{-# OPTIONS --safe #-}

module Core.Syntax.Derived where

open import Data.Fin using (zero; suc)

open import Core.Syntax
open import Core.Syntax.Renaming

infixr 3 _⇒'_
_⇒'_ : CExpr ℓ → CExpr ℓ → CExpr ℓ
τ₁ ⇒' τ₂ = CΠ τ₁ (weaken-ε τ₂)

⟨_⋆⋆_⟩ : CExpr ℓ → CExpr (suc ℓ) → CExpr ℓ
⟨ τ ⋆⋆ Px ⟩ = CΠ
               ⋆ₑ {- α -}
               (CΠ
                  (weaken-ε τ) {- x -}
                  (weaken-ε Px · CVar zero {- x -}
                   ⇒'
                   CVar (suc zero) {- α -})
                ⇒'
                CVar zero {- α -})

⟨_×_⟩ : CExpr ℓ → CExpr ℓ → CExpr ℓ
⟨ τ₁ × τ₂ ⟩ = ⟨ τ₁ ⋆⋆ weaken-ε τ₂ ⟩

_≡̂_of_ : CExpr ℓ → CExpr ℓ → CExpr ℓ → CExpr ℓ
ε₁ ≡̂ ε₂ of τ = CΠ (τ ⇒' ⋆ₑ) ⟨ CVar zero · weaken-ε ε₁ ⇒' CVar zero · weaken-ε ε₂
                            × CVar zero · weaken-ε ε₂ ⇒' CVar zero · weaken-ε ε₁
                            ⟩

eq-refl : CExpr ℓ → CExpr ℓ → CExpr ℓ
eq-refl τ x = CLam (τ ⇒' ⋆ₑ) ⟨ CLam (CVar zero · weaken-ε x) (CVar zero)
                             × CLam (CVar zero · weaken-ε x) (CVar zero)
                             ⟩
