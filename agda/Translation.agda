{-# OPTIONS --safe #-}

open import Surface.Derivations.Algorithmic using (UniquenessOfOracles)

module Translation(oracles-equal : UniquenessOfOracles) where

open import Data.Fin using (zero)
open import Data.Vec using (Vec; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

open import Core.Syntax as C renaming (Γ to Γᶜ; ε to εᶜ; τ to τᶜ)
open import Core.Syntax.Derived as C
open import Core.Syntax.Derived.Typing as C
open import Core.Syntax.Membership as C renaming (_∈_at_ to _∈ᶜ_at_)
open import Core.Syntax.Renaming as CR
open import Core.Derivations as C renaming (_⊢_⦂_ to _⊢ᶜ_⦂_)
open import Core.Derivations.Lemmas
open import Core.Operational as C
open import Core.Operational.BetaEquivalence as C
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; ε to εˢ)
open import Surface.Syntax.Membership as S renaming (_∈_at_ to _∈ˢ_at_)
open import Surface.Derivations.Algorithmic as S
open import Surface.Derivations.Algorithmic.Theorems.Agreement as S
open import Surface.Derivations.Algorithmic.Theorems.Uniqueness(oracles-equal)

open import Translation.Untyped
open import Translation.Typed
open import Translation.μ-weakening

μ-Τ-well-typed : Γᶜ ⊢ᶜ ⋆ₑ ⦂ □ₑ
               → Γᶜ ⊢ᶜ ⌊μ⌋-Τ ⦂ ⋆ₑ
μ-Τ-well-typed δ = ≡̂-well-typed (CT-UnitTerm δ) (CT-UnitTerm δ) (CT-UnitType δ)

μ-b-well-typed : Γᶜ ⊢ᶜ ⋆ₑ ⦂ □ₑ
               → Γᶜ ⊢ᶜ ⌊μ⌋-b b ⦂ ⋆ₑ
μ-b-well-typed {b = BUnit} Γᶜok =
  Σ-well-typed
    Γ⊢CUnit
    (CT-Abs
      (μ-Τ-well-typed Γ,CUnit-ok)
      (CT-Form Γ⊢CUnit Γ,CUnit-ok)
    )
  where
  Γ⊢CUnit = CT-UnitType Γᶜok
  Γ,CUnit-ok = Γ⊢τ-⇒-Γ,τ-ok Γ⊢CUnit

μ-preserves-∈ : (Γok : Γˢ ok[ E ])
              → (∈ : τˢ ∈ˢ Γˢ at ι)
              → μ-τ (τ∈Γ-⇒-Γ⊢τ Γok ∈) ∈ᶜ μ-Γ Γok at ι
μ-preserves-∈ (TCTX-Bind Γok τδ) (∈-zero refl) = ∈-zero (μ-τ-weakening-commutes Γok τδ τδ)
μ-preserves-∈ (TCTX-Bind Γok τδ) (∈-suc refl ∈) = ∈-suc (μ-τ-weakening-commutes Γok τδ (τ∈Γ-⇒-Γ⊢τ Γok ∈)) (μ-preserves-∈ Γok ∈)

subst-Γ : {Γok₁ Γok₂ : Γˢ ok[ E ]}
        → μ-Γ Γok₁ ⊢ᶜ εᶜ ⦂ τᶜ
        → μ-Γ Γok₂ ⊢ᶜ εᶜ ⦂ τᶜ
subst-Γ = subst (_⊢ᶜ _ ⦂ _) (cong μ-Γ (unique-Γok _ _))

mutual
  μ-b-P-well-typed : Γᶜ ⊢ᶜ ⋆ₑ ⦂ □ₑ
                   → Γᶜ ⊢ᶜ CΠ (⌊μ⌋-b b) ⋆ₑ ⦂ □ₑ
  μ-b-P-well-typed Γᶜok
    = let μ-b-ok = μ-b-well-typed Γᶜok
       in CT-Form
            μ-b-ok
            (Γ⊢τ-⇒-Γ,τ-ok μ-b-ok)

  μ-Γ-well-typed : (Γok : Γˢ ok[ E ])
                 → μ-Γ Γok ⊢ᶜ ⋆ₑ ⦂ □ₑ
  μ-Γ-well-typed TCTX-Empty = CT-Sort
  μ-Γ-well-typed (TCTX-Bind Γok τδ) = CT-Weaken (μ-Γ-well-typed Γok) (subst-Γ (μ-τ-well-typed τδ))

  μ-τ-well-typed : (τδ : Γˢ ⊢[ E ] τˢ)
                 → μ-Γ (Γ⊢τ-⇒-Γok τδ) ⊢ᶜ μ-τ τδ ⦂ ⋆ₑ
  μ-τ-well-typed δ = {! !}

  μ-ε-well-typed : (εδ : Γˢ ⊢[ E ] εˢ ⦂ τˢ)
                 → μ-Γ (Γ⊢ε⦂τ-⇒-Γok εδ) ⊢ᶜ μ-ε εδ ⦂ μ-τ (Γ⊢ε⦂τ-⇒-Γ⊢τ εδ)
  μ-ε-well-typed (T-Unit Γok) = {! !}
  μ-ε-well-typed (T-Var Γok ∈) = let r = μ-τ-well-typed (τ∈Γ-⇒-Γ⊢τ Γok ∈) in CT-VarW {! !} (μ-preserves-∈ Γok ∈)
  μ-ε-well-typed (T-Abs arrδ δ) = {! !}
  μ-ε-well-typed (T-App ε₁δ ε₂δ _ _ _) = {! !}
  μ-ε-well-typed (T-Case resδ δ branches-well-typed) = {! !}
  μ-ε-well-typed (T-Con ≡-prf δ adtτ) = {! !}
