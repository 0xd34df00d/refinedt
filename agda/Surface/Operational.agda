{-# OPTIONS --safe #-}

module Surface.Operational where

open import Surface.Syntax
open import Surface.Substitutions

data IsValue : STerm → Set where
  IV-Abs  : IsValue (SLam x τ ε)
  IV-Unit : IsValue SUnit
  IV-ADT  : ∀ {cons} {idx : Fin n}
          → IsValue ϖ
          → IsValue (SCon idx ϖ cons)

data _↝_ : STerm → STerm → Set where
  E-AppL      : ε₁ ↝ ε₁'
              → SApp ε₁ ε₂ ↝ SApp ε₁' ε₂
  E-AppR      : IsValue ϖ
              → ε₂ ↝ ε₂'
              → SApp ϖ ε₂ ↝ SApp ϖ ε₂'
  E-AppAbs    : IsValue ϖ
              → SApp (SLam x τ ε) ϖ ↝ [ x ↦ₑ ϖ ] ε
  E-ADT       : ∀ {cons} {idx : Fin n}
              → ε ↝ ε'
              → SCon idx ε cons ↝ SCon idx ε' cons
  E-CaseScrut : ∀ {branches : CaseBranches n}
              → ε ↝ ε'
              → SCase ε branches ↝ SCase ε' branches
  E-CaseMatch : ∀ {idx} {cons : ADTCons n} {branches : CaseBranches n}
              → SCase (SCon idx ε cons) branches ↝ [ idx ↦ₘ ε ] branches
