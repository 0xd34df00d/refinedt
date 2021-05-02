{-# OPTIONS --safe #-}

module Surface.Operational where

open import Data.Fin using (zero)
open import Data.Vec

open import Surface.Syntax
open import Surface.Syntax.Substitution

data IsValue : STerm ℓ → Set where
  IV-Abs  : IsValue (SLam τ ε)
  IV-Unit : IsValue (SUnit {ℓ})
  IV-ADT  : ∀ {cons} {ι : Fin n}
          → IsValue ϖ
          → IsValue (SCon ι ϖ cons)

infix 6 [_↦ₘ_]_
[_↦ₘ_]_ : Fin n → STerm ℓ → CaseBranches (Mkℕₐ n) ℓ → STerm ℓ
[ ι ↦ₘ ε ] bs = [ zero ↦ε ε ] body
  where open CaseBranch (lookup bs ι)

infix 4 _↝_
data _↝_ : STerm ℓ → STerm ℓ → Set where
  E-AppL      : ε₁ ↝ ε₁'
              → SApp ε₁ ε₂ ↝ SApp ε₁' ε₂
  E-AppR      : IsValue ϖ
              → ε₂ ↝ ε₂'
              → SApp ϖ ε₂ ↝ SApp ϖ ε₂'
  E-AppAbs    : IsValue ϖ
              → SApp (SLam τ ε) ϖ ↝ [ zero ↦ε ϖ ] ε
  E-ADT       : ∀ {cons} {ι : Fin n}
              → ε ↝ ε'
              → SCon ι ε cons ↝ SCon ι ε' cons
  E-CaseScrut : ∀ {branches : CaseBranches nₐ ℓ}
              → ε ↝ ε'
              → SCase ε branches ↝ SCase ε' branches
  E-CaseMatch : ∀ {cons : ADTCons (Mkℕₐ n) ℓ} {bs : CaseBranches (Mkℕₐ n) ℓ}
              → IsValue ϖ
              → (ι : Fin n)
              → SCase (SCon ι ϖ cons) bs ↝ [ ι ↦ₘ ϖ ] bs
