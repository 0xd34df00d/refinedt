module Surface.Operational where

open import Surface.Syntax
open import Surface.Substitutions

data IsValue : STerm → Set where
  IV-Abs  : IsValue (SLam x τ ε)
  IV-Unit : IsValue SUnit
  IV-ADT  : ∀ {idx cons}
          → IsValue ε
          → IsValue (SCon idx ε cons)

data _↝_ : STerm → STerm → Set where
  E-AppL      : ε₁ ↝ ε₁'
              → SApp ε₁ ε₂ ↝ SApp ε₁' ε₂
  E-AppR      : IsValue ε₁
              → ε₂ ↝ ε₂'
              → SApp ε₁ ε₂ ↝ SApp ε₁ ε₂'
  E-AppAbs    : IsValue ε₂
              → SApp (SLam x τ ε) ε₂ ↝ [ x ↦ₑ ε₂ ] ε
  E-ADT       : ∀ {idx cons}
              → ε ↝ ε'
              → SCon idx ε cons ↝ SCon idx ε' cons
  E-CaseScrut : ∀ {branches}
              → ε ↝ ε'
              → SCase ε branches ↝ SCase ε' branches
  E-CaseMatch : ∀ {idx} {cons : ADTCons n} {branches : CaseBranches n}
              → SCase (SCon idx ε cons) branches ↝ [ idx ↦ₘ ε ] branches
