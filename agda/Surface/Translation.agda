module Surface.Translation where

open import Data.Fin using (zero; suc)
open import Data.Vec using (Vec; _∷_; []; lookup)
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

open import Surface.Translation.Untyped
open import Surface.Translation.Typed
open import Surface.Translation.SubstUnique
open import Surface.Translation.Helpers
open import Surface.Translation.μ-subst

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

μ-b-P-well-typed : Γᶜ ⊢ᶜ ⋆ₑ ⦂ □ₑ
                 → Γᶜ ⊢ᶜ CΠ (⌊μ⌋-b b) ⋆ₑ ⦂ □ₑ
μ-b-P-well-typed Γᶜok
  = let μ-b-ok = μ-b-well-typed Γᶜok
     in CT-Form
          μ-b-ok
          (Γ⊢τ-⇒-Γ,τ-ok μ-b-ok)

mutual
  μ-Γ-well-typed : (Γok : Γˢ ok[ θ , E ])
                 → μ-Γ Γok ⊢ᶜ ⋆ₑ ⦂ □ₑ
  μ-Γ-well-typed TCTX-Empty = CT-Sort
  μ-Γ-well-typed (TCTX-Bind Γok τδ) = CT-Weaken (μ-Γ-well-typed Γok) (subst-Γ _ _ (μ-τ-well-typed τδ))

  μ-τ-well-typed : (τδ : Γˢ ⊢[ θ , E ] τˢ)
                 → μ-Γ (Γ⊢τ-⇒-Γok τδ) ⊢ᶜ μ-τ τδ ⦂ ⋆ₑ
  μ-τ-well-typed (TWF-TrueRef Γok) = μ-b-well-typed (μ-Γ-well-typed Γok)
  μ-τ-well-typed (TWF-Base ε₁δ ε₂δ) = {! !}
  μ-τ-well-typed (TWF-Conj τ₁δ τ₂δ) = let μ-τ₂δ-well-typed = μ-τ-well-typed τ₂δ
                                          μ-τ₂δ-well-typed' = subst-Γ (Γ⊢τ-⇒-Γok τ₂δ) (Γ⊢τ-⇒-Γok τ₁δ) μ-τ₂δ-well-typed
                                       in ×-well-typed (μ-τ-well-typed τ₁δ) μ-τ₂δ-well-typed'
  μ-τ-well-typed (TWF-Arr domδ codδ) = let μ-τ-domδ = μ-τ-well-typed domδ
                                           μ-τ-codδ = μ-τ-well-typed codδ
                                           μ-Γ-≡ = μ-Γ-distributes-over-, (Γ⊢τ-⇒-Γok codδ) (Γ⊢τ-⇒-Γok domδ) domδ
                                           μ-τ-codδ' = subst (_⊢ᶜ μ-τ codδ ⦂ ⋆ₑ) μ-Γ-≡ μ-τ-codδ
                                        in CT-Form μ-τ-domδ μ-τ-codδ'
  μ-τ-well-typed (TWF-ADT consδs@(τδ ∷ _)) = CT-ADTForm (μ-cons-well-typed consδs (Γ⊢τ-⇒-Γok τδ))

  μ-cons-well-typed : {cons : S.ADTCons nₐ ℓ}
                    → (consδs : All (Γˢ ⊢[ θ , E ]_) cons)
                    → (Γok : Γˢ ok[ θ , E ])
                    → All (λ con → μ-Γ Γok ⊢ᶜ con ⦂ ⋆ₑ) (μ-cons consδs)
  μ-cons-well-typed [] _ = []
  μ-cons-well-typed (τδ ∷ consδs) Γok = subst-Γ _ _ (μ-τ-well-typed τδ) ∷ μ-cons-well-typed consδs Γok

  μ-ε-well-typed : (εδ : Γˢ ⊢[ θ , E of not-t-sub ] εˢ ⦂ τˢ)
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
  μ-ε-well-typed (T-App ε₁δ (T-Sub {τ = τ₁'} ε₂δ τ'δ <:δ) refl resτδ) with TWF-Arr τ₁δ τ₂δ ← Γ⊢ε⦂τ-⇒-Γ⊢τ ε₁δ
    = let ε₁δᶜ = subst-τ (Γ⊢ε⦂τ-⇒-Γ⊢τ ε₁δ) (TWF-Arr τ₁δ τ₂δ) (μ-ε-well-typed ε₁δ)
          ε₂δᶜ = ⇒'-·-well-typed {τ₂ = μ-τ τ'δ}
                  (μ-<:-well-typed (Γ⊢ε⦂τ-⇒-Γok ε₂δ) (Γ⊢ε⦂τ-⇒-Γ⊢τ ε₂δ) τ'δ <:δ) 
                  (μ-ε-well-typed ε₂δ)
          ε₂δᶜ = subst-Γ (Γ⊢ε⦂τ-⇒-Γok ε₂δ) (Γ⊢ε⦂τ-⇒-Γok ε₁δ)
                   (subst-τ τ'δ τ₁δ
                     ε₂δᶜ)
          app = CT-App ε₁δᶜ ε₂δᶜ
          ret-eq = μ-τ-sub-front-distributes ε₂δ <:δ τ₂δ resτδ
       in {! !} -- subst (_ ⊢ᶜ _ ⦂_) (sym (ret-eq)) app
  μ-ε-well-typed (T-Case resδ δ branches-well-typed) = {! !}
  μ-ε-well-typed (T-Con refl δ τδ@(TWF-ADT consδs))
    = let ≡-prf = μ-lookup-commutes _ consδs (Γ⊢ε⦂τ-⇒-Γ⊢τ δ)
          εδᶜ = μ-ε-well-typed δ
          τδᶜ = subst-Γ _ _ (μ-τ-well-typed τδ)
       in CT-ADTCon ≡-prf εδᶜ τδᶜ

  μ-<:-well-typed : (Γok : Γˢ ok[ θ , E ])
                  → (τδ : Γˢ ⊢[ θ , E ] τˢ)
                  → (τ'δ : Γˢ ⊢[ θ , E ] τ'ˢ)
                  → (<:δ : Γˢ ⊢[ θ , E ] τˢ <: τ'ˢ)
                  → μ-Γ Γok ⊢ᶜ μ-<: <:δ ⦂ μ-τ τδ ⇒' μ-τ τ'δ
  μ-<:-well-typed = {! !}
