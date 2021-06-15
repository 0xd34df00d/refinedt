{-# OPTIONS --safe #-}

module Translation where

open import Data.Fin using (zero)
open import Data.Vec using (Vec; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Syntax as C renaming (Γ to Γᶜ)
open import Core.Syntax.Derived as C
open import Core.Syntax.Derived.Typing as C
open import Core.Derivations as C renaming (_⊢_⦂_ to _⊢ᶜ_⦂_)
open import Core.Derivations.Lemmas
open import Core.Operational as C
open import Core.Operational.BetaEquivalence as C
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; ε to εˢ)
open import Surface.Derivations as S renaming (_⊢_⦂_ to _⊢ˢ_⦂_)
open import Surface.Theorems.Agreement.Γok

open import Translation.Untyped
open import Translation.Untyped.Lemmas.Misc using (⌊μ⌋-lookup-commute)
open import Translation.Untyped.Lemmas.RenamingCommutativity using (⌊μ⌋-Γ-preserves-∈)
open import Translation.Untyped.Lemmas.SubstCommutativity using (⌊μ⌋-τ-preserves-↦)

μ-Τ-well-formed : Γᶜ ⊢ᶜ ⋆ₑ ⦂ □ₑ
                → Γᶜ ⊢ᶜ ⌊μ⌋-Τ ⦂ ⋆ₑ
μ-Τ-well-formed δ = ≡̂-well-typed (CT-UnitTerm δ) (CT-UnitTerm δ) (CT-UnitType δ)

mutual
  μ-Γ-well-formed : Γˢ ok
                  → ⌊μ⌋-Γ Γˢ ⊢ᶜ ⋆ₑ ⦂ □ₑ
  μ-Γ-well-formed TCTX-Empty = CT-Sort
  μ-Γ-well-formed (TCTX-Bind Γok τδ) = CT-Weaken (μ-Γ-well-formed Γok) (μ-τ τδ)

  μ-Γ-well-formed-ε : Γˢ ⊢ˢ εˢ ⦂ τˢ
                    → ⌊μ⌋-Γ Γˢ ⊢ᶜ ⋆ₑ ⦂ □ₑ
  μ-Γ-well-formed-ε δε = Γ⊢⋆⦂□ (μ-ε δε)

  μ-b : ⌊μ⌋-Γ Γˢ ⊢ᶜ ⋆ₑ ⦂ □ₑ
      → ∀ b
      → ⌊μ⌋-Γ Γˢ ⊢ᶜ ⌊μ⌋-b b ⦂ ⋆ₑ
  μ-b Γok BUnit =
    Σ-well-typed
      (CT-UnitType Γok)
      (CT-Abs
        (μ-Τ-well-formed Γ,CUnit-ok)
        (CT-Form Γˢ⊢CUnit Γ,CUnit-ok)
      )
    where
    Γˢ⊢CUnit = CT-UnitType Γok
    Γ,CUnit-ok = Γ⊢τ-⇒-Γ,τ-ok Γˢ⊢CUnit

  μ-b-P : ⌊μ⌋-Γ Γˢ ⊢ᶜ ⋆ₑ ⦂ □ₑ
        → ⌊μ⌋-Γ Γˢ ⊢ᶜ CΠ (⌊μ⌋-b b) ⋆ₑ ⦂ □ₑ
  μ-b-P Γok = CT-Form
                (μ-b Γok _)
                (Γ⊢τ-⇒-Γ,τ-ok (μ-b Γok _))

  μ-ρ : ∀ {ρ}
      → Γˢ ⊢ ⟨ b ∣ ρ ⟩
      → ⌊μ⌋-Γ Γˢ , ⌊μ⌋-b b ⊢ᶜ ⌊μ⌋-ρ ρ ⦂ ⋆ₑ
  μ-ρ (TWF-TrueRef Γok) = μ-Τ-well-formed (Γ⊢τ-⇒-Γ,τ-ok (μ-b (μ-Γ-well-formed Γok) _))
  μ-ρ (TWF-Base δε₁ δε₂) = ≡̂-well-typed (μ-ε δε₁) (μ-ε δε₂) (μ-b (Γ⊢⋆⦂□ (μ-ε δε₁)) _)
  μ-ρ (TWF-Conj δρ₁ δρ₂) = ×-well-typed (μ-ρ δρ₁) (μ-ρ δρ₂)

  μ-τ : Γˢ ⊢ τˢ
      → ⌊μ⌋-Γ Γˢ ⊢ᶜ ⌊μ⌋-τ τˢ ⦂ ⋆ₑ
  μ-τ (TWF-TrueRef Γok) = μ-b (μ-Γ-well-formed Γok) _
  μ-τ Γ⊢τ@(TWF-Base δε₁ δε₂) =
    let δε̂₁ = μ-ε δε₁
        δε̂₂ = μ-ε δε₂
        sub-Γok = μ-Γ-well-formed-ε δε₁
        Γok = Γ,τ-ok-⇒-Γ-ok sub-Γok
     in Σ-well-typed
          (μ-b Γok _)
          (CT-Abs
            (≡̂-well-typed δε̂₁ δε̂₂ (μ-b sub-Γok _))
            (μ-b-P Γok)
          )
  μ-τ (TWF-Conj δρ₁ δρ₂) =
    let Γok = Γ,τ-ok-⇒-Γ-ok (Γ⊢τ-⇒-Γ,τ-ok (μ-τ δρ₁))
     in Σ-well-typed
          (μ-b Γok _)
          (CT-Abs
            (×-well-typed (μ-ρ δρ₁) (μ-ρ δρ₂))
            (μ-b-P Γok)
          )
  μ-τ (TWF-Arr Γ⊢τ₁ Γ⊢τ₂) = CT-Form (μ-τ Γ⊢τ₁) (μ-τ Γ⊢τ₂)
  μ-τ (TWF-ADT consδs) = CT-ADTForm (μ-cons consδs)

  μ-ε : Γˢ ⊢ˢ εˢ ⦂ τˢ
      → ⌊μ⌋-Γ Γˢ ⊢ᶜ ⌊μ⌋-ε εˢ ⦂ ⌊μ⌋-τ τˢ
  μ-ε (T-Unit Γok) =
    let Γ̂ok = μ-Γ-well-formed Γok
        Γ̂⊢CUnit = CT-UnitType Γ̂ok
        eq-refl-wt = eq-refl-well-typed (CT-UnitType Γ̂ok) (CT-UnitTerm Γ̂ok)
        λ:CUnit[μ-Τ] = CT-Abs
                          (μ-Τ-well-formed (Γ⊢τ-⇒-Γ,τ-ok Γ̂⊢CUnit))
                          (CT-Form Γ̂⊢CUnit (Γ⊢τ-⇒-Γ,τ-ok Γ̂⊢CUnit))
     in Σ-ctor-well-typed
         Γ̂⊢CUnit
         λ:CUnit[μ-Τ]
         (CT-UnitTerm Γ̂ok)
         (CT-Conv
           eq-refl-wt
           (CT-App
             λ:CUnit[μ-Τ]
             (CT-UnitTerm Γ̂ok)
           )
           (↜-as-↭β (CE-AppAbs IV-unit))
         )
  μ-ε (T-Var Γok ∈) = CT-VarW (μ-Γ-well-formed Γok) (⌊μ⌋-Γ-preserves-∈ ∈)
  μ-ε (T-Abs arrδ δε) = CT-Abs (μ-ε δε) (μ-τ arrδ)
  μ-ε (T-App {τ₂ = τ₂} {ε₂ = ε₂} δε₁ δε₂)
    rewrite ⌊μ⌋-τ-preserves-↦ zero ε₂ τ₂
          = CT-App (μ-ε δε₁) (μ-ε δε₂)
  μ-ε (T-Case resδ δε δbranches) = CT-ADTCase (μ-τ resδ) (μ-ε δε) (μ-branches δε δbranches)
  μ-ε (T-Con {ι = ι} {cons = cons} refl δε adtτ) = CT-ADTCon (⌊μ⌋-lookup-commute cons ι) (μ-ε δε) (μ-τ adtτ)
  μ-ε (T-Sub δε τ'δ <:) = {! !}
  μ-ε (T-RConv δε τ'δ τ~τ') = CT-Conv (μ-ε δε) (μ-τ τ'δ) {! !}

  μ-cons : {cons : S.ADTCons nₐ ℓ}
         → All (Γˢ ⊢_) cons
         → All (λ con → ⌊μ⌋-Γ Γˢ ⊢ᶜ con ⦂ ⋆ₑ) (⌊μ⌋-cons cons)
  μ-cons [] = []
  μ-cons (δτ ∷ consδs) = μ-τ δτ ∷ μ-cons consδs

  μ-branches : {cons : S.ADTCons nₐ ℓ}
             → {bs : S.CaseBranches nₐ ℓ}
             → Γˢ ⊢ˢ εˢ ⦂ (⊍ cons)
             → S.BranchesHaveType Γˢ cons bs τˢ
             → C.BranchesHaveType
                   (⌊μ⌋-Γ Γˢ)
                   (⌊μ⌋-ε εˢ)
                   (⌊μ⌋-cons cons)
                   (⌊μ⌋-branches bs)
                   (⌊μ⌋-τ τˢ)
  μ-branches δε bht ι = {! !}
