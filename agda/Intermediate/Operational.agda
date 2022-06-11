{-# OPTIONS --safe #-}

module Intermediate.Operational where

open import Data.Fin using (zero)
open import Data.Vec

open import Intermediate.Syntax
open import Intermediate.Syntax.Substitution

data IsValue : ITerm ℓ → Set where
  IV-Abs  : IsValue (ILam τ ε)
  IV-Unit : IsValue (IUnit {ℓ})
  IV-ADT  : ∀ {cons} {ι : Fin n}
          → IsValue ϖ
          → IsValue (ICon ι ϖ cons)
  IV-I<:  : IsValue ϖ
          → IsValue (ϖ I<: τ)

infix 6 [_↦ₘ_]_
[_↦ₘ_]_ : Fin n → ITerm ℓ → CaseBranches (Mkℕₐ n) ℓ → ITerm ℓ
[ ι ↦ₘ ε ] bs = [ zero ↦ε ε ] body
  where open CaseBranch (lookup bs ι)

infix 4 _↝_
data _↝_ : ITerm ℓ → ITerm ℓ → Set where
  E-AppL      : ε₁ ↝ ε₁'
              → IApp ε₁ ε₂ ↝ IApp ε₁' ε₂
  E-AppAbs    : IApp (ILam τ ε) ε' ↝ [ zero ↦ε ε' ] ε
  E-ADT       : ∀ {cons} {ι : Fin n}
              → ε ↝ ε'
              → ICon ι ε cons ↝ ICon ι ε' cons
  E-CaseScrut : ∀ {branches : CaseBranches nₐ ℓ}
              → ε ↝ ε'
              → ICase ε branches ↝ ICase ε' branches
  E-CaseMatch : ∀ {cons : ADTCons (Mkℕₐ n) ℓ} {bs : CaseBranches (Mkℕₐ n) ℓ}
              → IsValue ϖ
              → (ι : Fin n)
              → ICase (ICon ι ϖ cons) bs ↝ [ ι ↦ₘ ϖ ] bs
  E-I<:       : ε ↝ ε'
              → ε I<: τ ↝ ε' I<: τ

data _↝⋆_ : ITerm ℓ → ITerm ℓ → Set where
  ↝-refl  : ε ↝⋆ ε
  ↝-trans : ε₁ ↝ ε₂
          → ε₂ ↝⋆ ε₃
          → ε₁ ↝⋆ ε₃
