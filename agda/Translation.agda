{-# OPTIONS --safe #-}

module Translation where

open import Data.Fin using (zero)
open import Data.Vec using (Vec; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Syntax as C renaming (Γ to Γᶜ)
open import Core.Syntax.Derived as C
open import Core.Syntax.Derived.Typing as C
open import Core.Syntax.Renaming as CR
open import Core.Derivations as C renaming (_⊢_⦂_ to _⊢ᶜ_⦂_)
open import Core.Derivations.Lemmas
open import Core.Operational as C
open import Core.Operational.BetaEquivalence as C
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; ε to εˢ)
open import Surface.Derivations as S renaming (_⊢_⦂_ to _⊢ˢ_⦂_)
open import Surface.Theorems.Agreement.Γok
open import Surface.Operational.BetaEquivalence as S

open import Translation.Untyped
open import Translation.Typed

μ-Τ-well-typed : Γᶜ ⊢ᶜ ⋆ₑ ⦂ □ₑ
               → Γᶜ ⊢ᶜ ⌊μ⌋-Τ ⦂ ⋆ₑ
μ-Τ-well-typed δ = ≡̂-well-typed (CT-UnitTerm δ) (CT-UnitTerm δ) (CT-UnitType δ)

μ-b-well-typed : Γᶜ ⊢ᶜ ⋆ₑ ⦂ □ₑ
               → ∀ b
               → Γᶜ ⊢ᶜ ⌊μ⌋-b b ⦂ ⋆ₑ
μ-b-well-typed Γᶜok BUnit =
    Σ-well-typed
      Γ⊢CUnit
      (CT-Abs
        (μ-Τ-well-typed Γ,CUnit-ok)
        (CT-Form Γ⊢CUnit Γ,CUnit-ok)
      )
    where
    Γ⊢CUnit = CT-UnitType Γᶜok
    Γ,CUnit-ok = Γ⊢τ-⇒-Γ,τ-ok Γ⊢CUnit

mutual
  μ-Γ-well-typed : (Γok : Γˢ ok)
                 → μ-Γ Γok ⊢ᶜ ⋆ₑ ⦂ □ₑ
  μ-Γ-well-typed TCTX-Empty = CT-Sort
  μ-Γ-well-typed (TCTX-Bind Γok τδ) = CT-Weaken (μ-Γ-well-typed Γok) (μ-τ-well-typed Γok τδ)

  μ-b-P-well-typed : Γᶜ ⊢ᶜ ⋆ₑ ⦂ □ₑ
                   → Γᶜ ⊢ᶜ CΠ (⌊μ⌋-b b) ⋆ₑ ⦂ □ₑ
  μ-b-P-well-typed Γᶜok = CT-Form
                            μ-b-ok
                            (Γ⊢τ-⇒-Γ,τ-ok μ-b-ok)
    where
    μ-b-ok = (μ-b-well-typed Γᶜok _)

  μ-τ-well-typed : (Γok : Γˢ ok)
                 → (τδ : Γˢ ⊢ τˢ)
                 → μ-Γ Γok ⊢ᶜ μ-τ τδ ⦂ ⋆ₑ
  μ-τ-well-typed Γok (TWF-TrueRef x) = {! !}
  μ-τ-well-typed Γok (TWF-Base {b = b} ε₁δ ε₂δ) with Γ⊢ε⦂τ-⇒-Γok ε₁δ
  ... | Γ'ok@(TCTX-Bind _ _) =
    let ε̂₁δ = μ-ε-well-typed Γ'ok {! !} ε₁δ
     in Σ-well-typed
          (μ-b-well-typed (μ-Γ-well-typed Γok) b)
          (CT-Abs
            (≡̂-well-typed {! ε̂₁δ !} {! !} {! !})
            (μ-b-P-well-typed (μ-Γ-well-typed Γok))
          )
  μ-τ-well-typed Γok (TWF-Conj τδ₁ τδ₂) = ×-well-typed (μ-τ-well-typed Γok τδ₁) (μ-τ-well-typed Γok τδ₂)
  μ-τ-well-typed Γok (TWF-Arr τδ₁ τδ₂) = CT-Form (μ-τ-well-typed Γok τδ₁) (μ-τ-well-typed (TCTX-Bind Γok τδ₁) τδ₂)
  μ-τ-well-typed Γok (TWF-ADT consδs) = {! !}

  μ-ε-well-typed : (Γok : Γˢ ok)
                 → (τδ : Γˢ ⊢ τˢ)
                 → (εδ : Γˢ ⊢ˢ εˢ ⦂ τˢ)
                 → μ-Γ Γok ⊢ᶜ μ-ε εδ ⦂ μ-τ τδ
  μ-ε-well-typed Γok τδ εδ = {! !}
