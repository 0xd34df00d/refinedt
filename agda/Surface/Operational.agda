{-# OPTIONS --safe #-}

module Surface.Operational where

open import Data.Fin using (zero)
open import Data.Vec

open import Surface.WellScoped
open import Surface.WellScoped.Substitution

data IsValue : STerm ℓ → Set where
  IV-Abs  : IsValue (SLam τ ε)
  IV-Unit : IsValue (SUnit {ℓ})
  IV-ADT  : ∀ {cons} {idx : Fin n}
          → IsValue ϖ
          → IsValue (SCon idx ϖ cons)

infix 6 [_↦ₘ_]_
[_↦ₘ_]_ : Fin n → STerm ℓ → CaseBranches (Mkℕₐ n) ℓ → STerm ℓ
[ idx ↦ₘ ε ] bs = [ zero ↦ε ε ] body
  where open CaseBranch (lookup bs idx)

infix 4 _↝_
data _↝_ : STerm ℓ → STerm ℓ → Set where
  E-AppL      : ε₁ ↝ ε₁'
              → SApp ε₁ ε₂ ↝ SApp ε₁' ε₂
  E-AppR      : IsValue ϖ
              → ε₂ ↝ ε₂'
              → SApp ϖ ε₂ ↝ SApp ϖ ε₂'
  E-AppAbs    : IsValue ϖ
              → SApp (SLam τ ε) ϖ ↝ [ zero ↦ε ϖ ] ε
  E-ADT       : ∀ {cons} {idx : Fin n}
              → ε ↝ ε'
              → SCon idx ε cons ↝ SCon idx ε' cons
  E-CaseScrut : ∀ {branches : CaseBranches nₐ ℓ}
              → ε ↝ ε'
              → SCase ε branches ↝ SCase ε' branches
  E-CaseMatch : ∀ {idx : Fin n} {cons : ADTCons (Mkℕₐ n) ℓ} {bs : CaseBranches (Mkℕₐ n) ℓ}
              → IsValue ϖ
              → SCase (SCon idx ϖ cons) bs ↝ [ idx ↦ₘ ϖ ] bs
