open import Surface.Derivations.Algorithmic using (UniquenessOfOracles)

module Translation(oracles-equal : UniquenessOfOracles) where

open import Data.Fin using (zero)
open import Data.Vec using (Vec; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)

open import Core.Syntax as C renaming (Γ to Γᶜ; ε to εᶜ; τ to τᶜ)
open import Core.Syntax.Derived as C
open import Core.Syntax.Derived.Typing as C
open import Core.Syntax.Membership as C renaming (_∈_at_ to _∈ᶜ_at_)
open import Core.Syntax.Renaming as CR
open import Core.Syntax.Substitution as CS
open import Core.Derivations as C renaming (_⊢_⦂_ to _⊢ᶜ_⦂_)
open import Core.Derivations.Lemmas
open import Core.Operational as C
open import Core.Operational.BetaEquivalence as C
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; τ' to τ'ˢ; ε to εˢ)
open import Surface.Syntax.Membership as S renaming (_∈_at_ to _∈ˢ_at_)
open import Surface.Syntax.Substitution as SS
open import Surface.Derivations.Algorithmic as S
open import Surface.Derivations.Algorithmic.Theorems.Agreement as S
open import Surface.Derivations.Algorithmic.Theorems.Uniqueness(oracles-equal)

open import Translation.Untyped
open import Translation.Typed
open import Translation.μ-weakening(oracles-equal)
open import Translation.μ-subst

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

subst-Γ : (Γok₁ Γok₂ : Γˢ ok[ E ])
        → μ-Γ Γok₁ ⊢ᶜ εᶜ ⦂ τᶜ
        → μ-Γ Γok₂ ⊢ᶜ εᶜ ⦂ τᶜ
subst-Γ _ _ = subst (_⊢ᶜ _ ⦂ _) (cong μ-Γ (unique-Γok _ _))

subst-τ : (Γ⊢τ₁ Γ⊢τ₂ : Γˢ ⊢[ E ] τˢ)
        → Γᶜ ⊢ᶜ εᶜ ⦂ μ-τ Γ⊢τ₁
        → Γᶜ ⊢ᶜ εᶜ ⦂ μ-τ Γ⊢τ₂
subst-τ Γ⊢τ₁ Γ⊢τ₂ = subst (_ ⊢ᶜ _ ⦂_) (cong μ-τ (unique-Γ⊢τ Γ⊢τ₁ Γ⊢τ₂))

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
  μ-Γ-well-typed (TCTX-Bind Γok τδ) = CT-Weaken (μ-Γ-well-typed Γok) (subst-Γ _ _ (μ-τ-well-typed τδ))

  μ-τ-well-typed : (τδ : Γˢ ⊢[ E ] τˢ)
                 → μ-Γ (Γ⊢τ-⇒-Γok τδ) ⊢ᶜ μ-τ τδ ⦂ ⋆ₑ
  μ-τ-well-typed δ = {! !}

  μ-ε-well-typed : (εδ : Γˢ ⊢[ E of κ ] εˢ ⦂ τˢ)
                 → μ-Γ (Γ⊢ε⦂τ-⇒-Γok εδ) ⊢ᶜ μ-ε εδ ⦂ μ-τ (Γ⊢ε⦂τ-⇒-Γ⊢τ εδ)
  μ-ε-well-typed (T-Unit Γok)
    = let Γᶜok = μ-Γ-well-typed Γok
          Γᶜ⊢CUnit = CT-UnitType Γᶜok
          Γᶜ⊢Cunit⦂CUnit = CT-UnitTerm Γᶜok
          Γᶜ⊢λ[CUnit]μ-Τ⦂CUnit⇒⋆ = CT-Abs
              (μ-Τ-well-typed (CT-Weaken Γᶜok Γᶜ⊢CUnit))
              (CT-Form Γᶜ⊢CUnit (CT-Weaken Γᶜok Γᶜ⊢CUnit))
       in Σ-ctor-well-typed
            Γᶜ⊢CUnit
            Γᶜ⊢λ[CUnit]μ-Τ⦂CUnit⇒⋆
            Γᶜ⊢Cunit⦂CUnit
            (CT-Conv
              (eq-refl-well-typed Γᶜ⊢CUnit Γᶜ⊢Cunit⦂CUnit)
              (CT-App Γᶜ⊢λ[CUnit]μ-Τ⦂CUnit⇒⋆ Γᶜ⊢Cunit⦂CUnit)
              (↜-as-↭β CE-AppAbs))
  μ-ε-well-typed (T-Var Γok ∈) = CT-VarW (subst-Γ _ _ (μ-τ-well-typed (τ∈Γ-⇒-Γ⊢τ Γok ∈))) (μ-preserves-∈ Γok ∈)
  μ-ε-well-typed (T-Abs arrδ@(TWF-Arr domδ codδ) εδ)
    = let εδᶜ = subst-Γ _ (TCTX-Bind _ domδ)
                  (subst-τ (Γ⊢ε⦂τ-⇒-Γ⊢τ εδ) codδ
                    (μ-ε-well-typed εδ))
       in CT-Abs εδᶜ (μ-τ-well-typed arrδ)
  μ-ε-well-typed (T-App funδ argδ refl resτδ) with Γ⊢ε⦂τ-⇒-Γ⊢τ funδ
  ... | TWF-Arr domδ codδ
    = let funδᶜ = subst-τ (Γ⊢ε⦂τ-⇒-Γ⊢τ funδ) (TWF-Arr domδ codδ) (μ-ε-well-typed funδ)
          argδᶜ = μ-ε-well-typed argδ
          argδᶜ = subst-Γ (Γ⊢ε⦂τ-⇒-Γok argδ) (Γ⊢ε⦂τ-⇒-Γok funδ) argδᶜ
          argδᶜ = subst-τ (Γ⊢ε⦂τ-⇒-Γ⊢τ argδ) domδ argδᶜ
       in subst (_ ⊢ᶜ _ ⦂_) (sym (μ-τ-sub-front-commutes argδ codδ resτδ)) (CT-App funδᶜ argδᶜ)
  μ-ε-well-typed (T-Case resδ δ branches-well-typed) = {! !}
  μ-ε-well-typed (T-Con refl δ adtτ) = {! !}
  μ-ε-well-typed (T-Sub εδ τδ <:δ) = ⇒'-·-well-typed
                                      (μ-<:-well-typed (Γ⊢ε⦂τ-⇒-Γok εδ) (Γ⊢ε⦂τ-⇒-Γ⊢τ εδ) τδ <:δ)
                                      (μ-ε-well-typed εδ)

  μ-<:-well-typed : (Γok : Γˢ ok[ E ])
                  → (τδ : Γˢ ⊢[ E ] τˢ)
                  → (τ'δ : Γˢ ⊢[ E ] τ'ˢ)
                  → (<:δ : Γˢ ⊢[ E ] τˢ <: τ'ˢ)
                  → μ-Γ Γok ⊢ᶜ μ-<: <:δ ⦂ μ-τ τδ ⇒' μ-τ τ'δ
  μ-<:-well-typed = {! !}
