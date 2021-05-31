{-# OPTIONS --safe #-}

module Translation where

open import Data.Vec using (Vec; _∷_; [])

open import Core.Syntax as C renaming (Γ to Γᶜ)
open import Core.Syntax.Derived as C
open import Core.Syntax.Derived.Typing as C
open import Core.Derivations as C renaming (_⊢_⦂_ to _⊢ᶜ_⦂_)
open import Core.Derivations.Lemmas
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
  μ-b Γok BUnit =
    Σ-well-typed
      (CT-UnitType (μ-Γ-well-formed Γok))
      (CT-Abs
        (≡̂-well-typed (CT-UnitTerm Γ,CUnit-ok) (CT-UnitTerm Γ,CUnit-ok) (CT-UnitType Γ,CUnit-ok))
        (CT-Form Γˢ⊢CUnit Γ,CUnit-ok)
      )
    where
    Γˢ⊢CUnit = CT-UnitType (μ-Γ-well-formed Γok)
    Γ,CUnit-ok = Γ⊢τ-⇒-Γ,τ-ok Γˢ⊢CUnit

  μ-τ : Γˢ ⊢ τˢ
      → μ-Γ Γˢ ⊢ᶜ μ-τ-untyped τˢ ⦂ ⋆ₑ
  μ-τ (TWF-TrueRef Γok) = μ-b Γok _
  μ-τ (TWF-Base ε₁δ ε₂δ) = {! !}
  μ-τ (TWF-Conj Γ⊢τ₁ Γ⊢τ₂) = {! !}
  μ-τ (TWF-Arr Γ⊢τ₁ Γ⊢τ₂) = CT-Form (μ-τ Γ⊢τ₁) (μ-τ Γ⊢τ₂)
  μ-τ (TWF-ADT consδs) = {! !}
