{-# OPTIONS --safe #-}

module Translation.Untyped where

open import Data.Vec using (Vec; _∷_; [])

open import Core.Syntax as C
open import Core.Syntax.Derived as C
open import Core.Derivations as C
open import Surface.Syntax as S
open import Surface.Derivations as S

μ-Τ : CExpr ℓ
μ-Τ = Cunit ≡̂ Cunit of CUnit

μ-b-untyped : S.BaseType
            → CExpr ℓ
μ-b-untyped BUnit = Σ[ CUnit ] μ-Τ

mutual
  μ-τ-untyped : SType ℓ
              → CExpr ℓ
  μ-τ-untyped ⟨ b ∣ Τ ⟩ = μ-b-untyped b
  μ-τ-untyped ⟨ b ∣ ρ ⟩ = Σ[ μ-b-untyped b ] CLam (μ-b-untyped b) (μ-ρ-untyped ρ)
  μ-τ-untyped (τ₁ ⇒ τ₂) = CΠ (μ-τ-untyped τ₁) (μ-τ-untyped τ₂)
  μ-τ-untyped (⊍ cons) = CADT (μ-cons-untyped cons)

  μ-ρ-untyped : Refinement ℓ
              → CExpr ℓ
  μ-ρ-untyped Τ = μ-Τ
  μ-ρ-untyped (ε₁ ≈ ε₂ of τ) = μ-ε-untyped ε₁ ≡̂ μ-ε-untyped ε₂ of μ-τ-untyped τ
  μ-ρ-untyped (ρ₁ ∧ ρ₂) = ⟨ μ-ρ-untyped ρ₁ × μ-ρ-untyped ρ₂ ⟩

  μ-ε-untyped : STerm ℓ
              → CExpr ℓ
  μ-ε-untyped SUnit = Cunit
  μ-ε-untyped (SVar ι) = CVar ι
  μ-ε-untyped (SLam τ ε) = CLam (μ-τ-untyped τ) (μ-ε-untyped ε)
  μ-ε-untyped (SApp ε₁ ε₂) = μ-ε-untyped ε₁ · μ-ε-untyped ε₂
  μ-ε-untyped (SCase ε branches) = CCase (μ-ε-untyped ε) (μ-branches-untyped branches)
  μ-ε-untyped (SCon ι ε cons) = CCon ι (μ-ε-untyped ε) (μ-cons-untyped cons)

  μ-cons-untyped : S.ADTCons nₐ ℓ
                 → C.ADTCons nₐ ℓ
  μ-cons-untyped [] = []
  μ-cons-untyped (τ ∷ cons) = μ-τ-untyped τ ∷ μ-cons-untyped cons

  μ-branches-untyped : S.CaseBranches nₐ ℓ
                     → C.CaseBranches nₐ ℓ
  μ-branches-untyped [] = []
  μ-branches-untyped (MkCaseBranch ε ∷ bs) = {- TODO this is a placeholder proper proof -} Cunit ∷ μ-branches-untyped bs
