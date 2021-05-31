{-# OPTIONS --safe #-}

module Translation where

open import Data.Vec using (Vec; _∷_; [])

open import Core.Syntax as C renaming (Γ to Γᶜ)
open import Core.Syntax.Derived as C
open import Core.Syntax.Derived.Typing as C
open import Core.Derivations as C renaming (_⊢_⦂_ to _⊢ᶜ_⦂_)
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; ε to εˢ)
open import Surface.Derivations as S
open import Surface.Theorems.TCTX

open import Translation.Untyped

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
  μ-τ {Γˢ = Γˢ} (TWF-TrueRef {b = b} Γok) =
    Σ-well-typed
      (μ-b Γok b)
      (CT-Abs
        (≡̂-well-typed (CT-UnitTerm Γ̂,b-wf) (CT-UnitTerm Γ̂,b-wf) (CT-UnitType Γ̂,b-wf))
        (CT-Form
          (μ-b Γok b)
          Γ̂,b-wf
        )
      )
    where
    Γ̂,b-wf : μ-Γ Γˢ , μ-b-untyped b ⊢ᶜ ⋆ₑ ⦂ □ₑ
    Γ̂,b-wf = CT-Weaken (μ-Γ-well-formed Γok) (μ-b Γok b)
  μ-τ (TWF-Base ε₁δ ε₂δ) = {! !}
  μ-τ (TWF-Conj Γ⊢τ₁ Γ⊢τ₂) = {! !}
  μ-τ (TWF-Arr Γ⊢τ₁ Γ⊢τ₂) = CT-Form (μ-τ Γ⊢τ₁) (μ-τ Γ⊢τ₂)
  μ-τ (TWF-ADT consδs) = {! !}
