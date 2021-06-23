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
