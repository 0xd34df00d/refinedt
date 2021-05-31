{-# OPTIONS --safe #-}

module Translation where

open import Data.Vec using (Vec; _∷_; [])

open import Core.Syntax as C renaming (Γ to Γᶜ)
open import Core.Syntax.Derived as C
open import Core.Derivations as C renaming (_⊢_⦂_ to _⊢ᶜ_⦂_)
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; ε to εˢ)
open import Surface.Derivations as S

μ-b-untyped : S.BaseType
            → CExpr ℓ
μ-b-untyped BUnit = CUnit

mutual
  μ-τ-untyped : SType ℓ
              → CExpr ℓ
  μ-τ-untyped ⟨ b ∣ ρ ⟩ = Σ[ μ-b-untyped b ] CLam (μ-b-untyped b) (μ-ρ-untyped ρ)
  μ-τ-untyped (τ₁ ⇒ τ₂) = CΠ (μ-τ-untyped τ₁) (μ-τ-untyped τ₂)
  μ-τ-untyped (⊍ cons) = CADT (μ-cons-untyped cons)

  μ-ρ-untyped : Refinement ℓ
              → CExpr ℓ
  μ-ρ-untyped Τ = Cunit ≡̂ Cunit of CUnit
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
  μ-branches-untyped (MkCaseBranch ε ∷ bs) = {! TODO proof? !} ∷ μ-branches-untyped bs

μ-Γ : S.Ctx ℓ
    → C.Ctx ℓ
μ-Γ ⊘ = ⊘
μ-Γ (Γ , τ) = μ-Γ Γ , μ-τ-untyped τ

mutual
  μ-Γ-well-formed : Γˢ ok
                  → μ-Γ Γˢ ⊢ᶜ ⋆ₑ ⦂ □ₑ
  μ-Γ-well-formed TCTX-Empty = CT-Sort
  μ-Γ-well-formed (TCTX-Bind Γok τδ) = CT-Weaken (μ-Γ-well-formed Γok) (μ-τ τδ)

  μ-b : Γˢ ok
      → ∀ b
      → μ-Γ Γˢ ⊢ᶜ μ-b-untyped b ⦂ ⋆ₑ
  μ-b Γok BUnit = CT-UnitType (μ-Γ-well-formed Γok)

  μ-τ : Γˢ ⊢ τˢ
      → μ-Γ Γˢ ⊢ᶜ μ-τ-untyped τˢ ⦂ ⋆ₑ
  μ-τ (TWF-TrueRef Γok) = {! !}
  μ-τ (TWF-Base ε₁δ ε₂δ) = {! !}
  μ-τ (TWF-Conj Γ⊢τ₁ Γ⊢τ₂) = {! !}
  μ-τ (TWF-Arr Γ⊢τ₁ Γ⊢τ₂) = CT-Form (μ-τ Γ⊢τ₁) (μ-τ Γ⊢τ₂)
  μ-τ (TWF-ADT consδs) = {! !}
