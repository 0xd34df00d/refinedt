{-# OPTIONS --safe #-}

module Translation.Untyped where

open import Data.Vec using (Vec; _∷_; [])

open import Core.Syntax as C
open import Core.Syntax.Derived as C
open import Core.Derivations as C
open import Surface.Syntax as S

⌊μ⌋-Τ : CExpr ℓ
⌊μ⌋-Τ = Cunit ≡̂ Cunit of CUnit

⌊μ⌋-b : S.BaseType
      → CExpr ℓ
⌊μ⌋-b BUnit = Σ[ CUnit ] CLam CUnit ⌊μ⌋-Τ

mutual
  ⌊μ⌋-τ : SType ℓ
        → CExpr ℓ
  ⌊μ⌋-τ ⟨ b ∣ Τ ⟩ = ⌊μ⌋-b b
  ⌊μ⌋-τ ⟨ b ∣ ρ ⟩ = Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) (⌊μ⌋-ρ ρ)
  ⌊μ⌋-τ (τ₁ ⇒ τ₂) = CΠ (⌊μ⌋-τ τ₁) (⌊μ⌋-τ τ₂)
  ⌊μ⌋-τ (⊍ cons) = CADT (⌊μ⌋-cons cons)

  ⌊μ⌋-ρ : Refinement ℓ
        → CExpr ℓ
  ⌊μ⌋-ρ Τ = ⌊μ⌋-Τ
  ⌊μ⌋-ρ (ε₁ ≈ ε₂ of τ) = ⌊μ⌋-ε ε₁ ≡̂ ⌊μ⌋-ε ε₂ of ⌊μ⌋-τ τ
  ⌊μ⌋-ρ (ρ₁ ∧ ρ₂) = ⟨ ⌊μ⌋-ρ ρ₁ × ⌊μ⌋-ρ ρ₂ ⟩

  ⌊μ⌋-ε : STerm ℓ
        → CExpr ℓ
  ⌊μ⌋-ε SUnit = [ Cunit ⦂ CUnit ∣ eq-refl CUnit Cunit of (CLam CUnit ⌊μ⌋-Τ) ]
  ⌊μ⌋-ε (SVar ι) = CVar ι
  ⌊μ⌋-ε (SLam τ ε) = CLam (⌊μ⌋-τ τ) (⌊μ⌋-ε ε)
  ⌊μ⌋-ε (SApp ε₁ ε₂) = ⌊μ⌋-ε ε₁ · ⌊μ⌋-ε ε₂
  ⌊μ⌋-ε (SCase ε branches) = CCase (⌊μ⌋-ε ε) (⌊μ⌋-branches branches)
  ⌊μ⌋-ε (SCon ι ε cons) = CCon ι (⌊μ⌋-ε ε) (⌊μ⌋-cons cons)

  ⌊μ⌋-cons : S.ADTCons nₐ ℓ
           → C.ADTCons nₐ ℓ
  ⌊μ⌋-cons [] = []
  ⌊μ⌋-cons (τ ∷ cons) = ⌊μ⌋-τ τ ∷ ⌊μ⌋-cons cons

  ⌊μ⌋-branches : S.CaseBranches nₐ ℓ
               → C.CaseBranches nₐ ℓ
  ⌊μ⌋-branches [] = []
  ⌊μ⌋-branches (MkCaseBranch ε ∷ bs) = {- TODO this is a placeholder proper proof -} Cunit ∷ ⌊μ⌋-branches bs

⌊μ⌋-Γ : S.Ctx ℓ
      → C.Ctx ℓ
⌊μ⌋-Γ ⊘ = ⊘
⌊μ⌋-Γ (Γ , τ) = ⌊μ⌋-Γ Γ , ⌊μ⌋-τ τ
