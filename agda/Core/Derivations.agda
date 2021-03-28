{-# OPTIONS --safe #-}

module Core.Derivations where

open import Data.Fin using (zero)

open import Core.Syntax
open import Core.Syntax.Renaming
open import Core.Syntax.Substitution
open import Core.Operational

data _=β_ : CExpr ℓ → CExpr ℓ → Set where
  =-witness : ∀ ε
            → ε₁ ↝⋆ ε
            → ε₂ ↝⋆ ε
            → ε₁ =β ε₂

infix 2 _⊢_⦂_
data _⊢_⦂_ : Ctx ℓ → CExpr ℓ → CExpr ℓ → Set where
  CT-Sort : ⊘ ⊢ ⋆ₑ ⦂ □ₑ
  CT-Var : Γ ⊢ τ ⦂ CSort s
         → Γ , τ ⊢ CVar zero ⦂ weaken-ε τ
  CT-Weaken : Γ ⊢ ε₁ ⦂ τ₁
            → Γ ⊢ τ₂ ⦂ CSort s
            → Γ , τ₂ ⊢ weaken-ε ε₁ ⦂ weaken-ε τ₁
  CT-Form : Γ ⊢ τ₁ ⦂ CSort s₁
          → Γ , τ₁ ⊢ τ₂ ⦂ CSort s₂
          → Γ ⊢ CΠ τ₁ τ₂ ⦂ CSort s₂
  CT-App : Γ ⊢ ε₁ ⦂ CΠ τ₁ τ₂
         → Γ ⊢ ε₂ ⦂ τ₁
         → Γ ⊢ CApp ε₁ ε₂ ⦂ [ zero ↦ ε₂ ] τ₂
  CT-Abs : Γ , τ₁ ⊢ ε ⦂ τ₂
         → Γ ⊢ CΠ τ₁ τ₂ ⦂ CSort s
         → Γ ⊢ CLam τ₁ ε ⦂ CΠ τ₁ τ₂
  CT-Conv : Γ ⊢ ε ⦂ τ₁
          → Γ ⊢ τ₂ ⦂ CSort s
          → τ₁ =β τ₂
          → Γ ⊢ ε ⦂ τ₂
