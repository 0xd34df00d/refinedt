{-# OPTIONS --safe #-}

module Translation where

open import Data.Vec using (Vec; _∷_; [])

open import Core.Syntax as C renaming (Γ to Γᶜ)
open import Core.Syntax.Derived as C
open import Core.Syntax.Derived.Typing as C
open import Core.Derivations as C renaming (_⊢_⦂_ to _⊢ᶜ_⦂_)
open import Core.Derivations.Lemmas
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; ε to εˢ)
open import Surface.Derivations as S renaming (_⊢_⦂_ to _⊢ˢ_⦂_)
open import Surface.Theorems.TCTX

open import Translation.Untyped
open import Translation.Untyped.Lemmas

μ-Τ-well-formed : Γᶜ ⊢ᶜ ⋆ₑ ⦂ □ₑ
                → Γᶜ ⊢ᶜ μ-Τ ⦂ ⋆ₑ
μ-Τ-well-formed δ = ≡̂-well-typed (CT-UnitTerm δ) (CT-UnitTerm δ) (CT-UnitType δ)

mutual
  μ-Γ-well-formed : Γˢ ok
                  → μ-Γ Γˢ ⊢ᶜ ⋆ₑ ⦂ □ₑ
  μ-Γ-well-formed TCTX-Empty = CT-Sort
  μ-Γ-well-formed (TCTX-Bind Γok τδ) = CT-Weaken (μ-Γ-well-formed Γok) (μ-τ τδ)

  μ-Γ-well-formed-ε : Γˢ ⊢ˢ εˢ ⦂ τˢ
                    → μ-Γ Γˢ ⊢ᶜ ⋆ₑ ⦂ □ₑ
  μ-Γ-well-formed-ε δε = Γ⊢⋆⦂□ (μ-ε δε)

  μ-b : μ-Γ Γˢ ⊢ᶜ ⋆ₑ ⦂ □ₑ
      → ∀ b
      → μ-Γ Γˢ ⊢ᶜ μ-b-untyped b ⦂ ⋆ₑ
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

  μ-b-P : μ-Γ Γˢ ⊢ᶜ ⋆ₑ ⦂ □ₑ
        → μ-Γ Γˢ ⊢ᶜ CΠ (μ-b-untyped b) ⋆ₑ ⦂ □ₑ
  μ-b-P Γok = CT-Form
                (μ-b Γok _)
                (Γ⊢τ-⇒-Γ,τ-ok (μ-b Γok _))

  μ-ρ : ∀ {ρ}
      → Γˢ ⊢ ⟨ b ∣ ρ ⟩
      → μ-Γ Γˢ , μ-b-untyped b ⊢ᶜ μ-ρ-untyped ρ ⦂ ⋆ₑ
  μ-ρ (TWF-TrueRef Γok) = μ-Τ-well-formed (Γ⊢τ-⇒-Γ,τ-ok (μ-b (μ-Γ-well-formed Γok) _))
  μ-ρ (TWF-Base δε₁ δε₂) = ≡̂-well-typed (μ-ε δε₁) (μ-ε δε₂) (μ-b (Γ⊢⋆⦂□ (μ-ε δε₁)) _)
  μ-ρ (TWF-Conj δρ₁ δρ₂) = ×-well-typed (μ-ρ δρ₁) (μ-ρ δρ₂)

  μ-τ : Γˢ ⊢ τˢ
      → μ-Γ Γˢ ⊢ᶜ μ-τ-untyped τˢ ⦂ ⋆ₑ
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
  μ-τ (TWF-ADT consδs) = {! !}

  μ-ε : Γˢ ⊢ˢ εˢ ⦂ τˢ
      → μ-Γ Γˢ ⊢ᶜ μ-ε-untyped εˢ ⦂ μ-τ-untyped τˢ
  μ-ε (T-Unit Γok) =
    let Γ̂ok = μ-Γ-well-formed Γok
        Γ̂⊢CUnit = CT-UnitType Γ̂ok
     in Σ-ctor-well-typed {P = CLam CUnit μ-Τ} {π = eq-refl Cunit CUnit}
         Γ̂⊢CUnit
         (CT-Abs
           (μ-Τ-well-formed (Γ⊢τ-⇒-Γ,τ-ok Γ̂⊢CUnit))
           (CT-Form Γ̂⊢CUnit (Γ⊢τ-⇒-Γ,τ-ok Γ̂⊢CUnit))
         )
         (CT-UnitTerm Γ̂ok)
         {! !}
  μ-ε (T-Var Γok ∈) = CT-VarW (μ-Γ-well-formed Γok) (μ-Γ-preserves-∈ ∈)
  μ-ε (T-Abs arrδ δε) = CT-Abs (μ-ε δε) (μ-τ arrδ)
  μ-ε (T-App δε₁ δε₂) = {! !} -- CT-App {! μ-ε δε₁ !} (μ-ε δε₂)
  μ-ε (T-Case resδ δε branches-well-typed) = {! !}
  μ-ε (T-Con ≡-prf δε adtτ) = {! !}
  μ-ε (T-Sub δε τ'δ <:) = {! !}
  μ-ε (T-RConv δε τ'δ τ~τ') = {! !}
