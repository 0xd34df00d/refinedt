{-# OPTIONS --safe #-}

module Translation where

open import Data.Vec using (Vec; _∷_; [])

open import Core.Syntax as C
open import Core.Syntax.Derived as C
open import Core.Derivations as C
open import Surface.Syntax as S
open import Surface.Derivations as S

μ-b-untyped : S.BaseType
            → CExpr ℓ
μ-b-untyped BUnit = CUnit

mutual
  μ-τ-untyped : SType ℓ
              → CExpr ℓ
  μ-τ-untyped ⟨ b ∣ ρ ⟩ = ⟨ μ-b-untyped b ⋆⋆ μ-ρ-untyped ρ ⟩
  μ-τ-untyped (τ₁ ⇒ τ₂) = CΠ (μ-τ-untyped τ₁) (μ-τ-untyped τ₂)
  μ-τ-untyped (⊍ cons) = CADT (μ-cons-untyped cons)

  μ-ρ-untyped : Refinement ℓ
              → CExpr ℓ
  μ-ρ-untyped (ε₁ ≈ ε₂) = μ-ε-untyped ε₁ ≡̂ μ-ε-untyped ε₂ of {! !}
  μ-ρ-untyped (ρ₁ ∧ ρ₂) = ⟨ μ-ρ-untyped ρ₁ , μ-ρ-untyped ρ₂ ⟩

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
  μ-branches-untyped (MkCaseBranch ε ∷ bs) = {! !} ∷ μ-branches-untyped bs

μ-Γ : {Γ : S.Ctx ℓ}
    → Γ ok
    → C.Ctx ℓ
μ-τ : {Γ : S.Ctx ℓ}
    → {τ : SType ℓ}
    → Γ ⊢ τ
    → CExpr ℓ

μ-Γ TCTX-Empty = ⊘
μ-Γ (TCTX-Bind Γok τδ) = μ-Γ Γok , μ-τ τδ

μ-τ (TWF-TrueRef Γok) = {! !}
μ-τ (TWF-Base ε₁δ ε₂δ) = {! !}
μ-τ (TWF-Conj ρ₁δ ρ₂δ) = {! !}
μ-τ (TWF-Arr argδ resδ) = {! !}
μ-τ (TWF-ADT consδs) = {! !}
