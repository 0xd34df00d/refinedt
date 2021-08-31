{-# OPTIONS --safe #-}

module Core.Operational where

open import Data.Fin using (zero)
open import Data.Vec

open import Core.Syntax
open import Core.Syntax.Derived
open import Core.Syntax.Renaming
open import Core.Syntax.Substitution

data IsValue : CExpr ℓ → Set where
  IV-Abs  : IsValue (CLam ε₁ ε₂)
  IV-unit : IsValue (Cunit {ℓ})
  IV-ADT  : ∀ {cons} {idx : Fin n}
          → IsValue ϖ
          → IsValue (CCon idx ϖ cons)

infix 4 _↝_
data _↝_ : CExpr ℓ → CExpr ℓ → Set where
  CE-AppL : (ε₁↝ε₁' : ε₁ ↝ ε₁')
          → CApp ε₁ ε₂ ↝ CApp ε₁' ε₂
  CE-AppAbs : CApp (CLam τ ε) ϖ ↝ [ zero ↦ ϖ ] ε
  CE-ADT  : ∀ {cons} {idx : Fin n}
          → ε ↝ ε'
          → CCon idx ε cons ↝ CCon idx ε' cons
  CE-CaseScrut : ∀ {bs : CaseBranches nₐ ℓ}
               → ε ↝ ε'
               → CCase ε bs ↝ CCase ε' bs
  CE-CaseMatch : ∀ {cons : ADTCons (Mkℕₐ (suc n)) ℓ} {bs : CaseBranches (Mkℕₐ (suc n)) ℓ}
               → IsValue ϖ
               → (ι : Fin (suc n))
               → CCase (CCon ι ϖ cons) bs ↝ [ zero ↦ eq-refl (CADT cons) (CCon ι ϖ cons) ] [ zero ↦ weaken-ε ϖ ] lookup bs ι

data _↝⋆_ : CExpr ℓ → CExpr ℓ → Set where
  ↝-refl  : ε ↝⋆ ε
  ↝-trans : ε₁ ↝⋆ ε₂
          → ε₂ ↝ ε₃
          → ε₁ ↝⋆ ε₃
