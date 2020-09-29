{-# OPTIONS --safe #-}

module Core.Operational where

open import Core.Syntax

data IsValue : CExpr → Set where
  IV-Abs  : IsValue (CLam x ε₁ ε₂)
  IV-unit : IsValue Cunit
  IV-ADT  : ∀ {cons} {idx : Fin n}
          → IsValue ϖ
          → IsValue (CCon idx ϖ cons)

data _↝_ : CExpr → CExpr → Set where
  CE-AppL : ε₁ ↝ ε₂
          → CApp ε₁ ε₂ ↝ CApp ε₁' ε₂
  CE-AppR : IsValue ϖ
          → ε₂ ↝ ε₂'
          → CApp ϖ ε₂ ↝ CApp ϖ ε₂'
  CE-AppAbs : CApp (CLam x ε₁ ε₂) ϖ ↝ [ x ↦ ϖ ] ε₂
  CE-ADT  : ∀ {cons} {idx : Fin n}
          → ε ↝ ε'
          → CCon idx ε cons ↝ CCon idx ε' cons
  CE-CaseScrut : ∀ {bs : CaseBranches n}
               → ε ↝ ε'
               → CCase ε bs ↝ CCase ε' bs

data _↝⋆_ : CExpr → CExpr → Set where
  ↝-refl  : ε ↝⋆ ε
  ↝-trans : ε₁ ↝⋆ ε₂
          → ε₂ ↝ ε₃
          → ε₁ ↝⋆ ε₃
