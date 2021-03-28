{-# OPTIONS --safe #-}

module Core.Derivations where

{-
open import Agda.Builtin.Equality
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
-}

open import Core.Syntax
open import Core.Operational

data _=β_ : CExpr ℓ → CExpr ℓ → Set where
  =-witness : ∀ ε
            → ε₁ ↝⋆ ε
            → ε₂ ↝⋆ ε
            → ε₁ =β ε₂

infix 2 _⊢_⦂_
data _⊢_⦂_ : Ctx → CExpr → CExpr → Set where
  CT-Sort : [] ⊢ CSort ⋆ ⦂ CSort □
  CT-Var : Γ ⊢ ε ⦂ CSort s
         → Γ , ε ⊢ CVar zero ⦂ ε
  CT-Weaken : Γ ⊢ ε₁ ⦂ ε₂
            → Γ ⊢ ε₃ ⦂ CSort s
            → Γ , x ⦂ ε₃ ⊢ ε₁ ⦂ ε₂
  CT-Form : Γ ⊢ ε₁ ⦂ CSort s₁
          → Γ , x ⦂ ε₁ ⊢ ε₂ ⦂ CSort s₂
          → Γ ⊢ CPi x ε₁ ε₂ ⦂ CSort s₂
  CT-App : Γ ⊢ ε₁' ⦂ CPi x ε₁ ε₂
         → Γ ⊢ ε₂' ⦂ ε₁
         → Γ ⊢ CApp ε₁' ε₂' ⦂ [ x ↦ ε₂' ] ε₂
  CT-Abs : Γ , x ⦂ ε₁ ⊢ ε ⦂ ε₂
         → Γ ⊢ CPi x ε₁ ε₂ ⦂ CSort s
         → Γ ⊢ CLam x ε₁ ε ⦂ CPi x ε₁ ε₂
  CT-Conv : Γ ⊢ ε ⦂ ε₁
          → Γ ⊢ ε₂ ⦂ CSort s
          → ε₁ =β ε₂
          → Γ ⊢ ε ⦂ ε₂
