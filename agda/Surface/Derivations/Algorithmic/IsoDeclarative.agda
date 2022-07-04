module Surface.Derivations.Algorithmic.IsoDeclarative where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Vec.Relation.Unary.All using (All; _∷_; [])
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.Actions
open import Surface.Syntax.Renaming
open import Surface.Syntax.Substitution

import Surface.Derivations.Algorithmic as A
import Surface.Derivations.Algorithmic.Theorems.Agreement as A
import Surface.Derivations.Algorithmic.Theorems.Subtyping as A
open import Surface.Derivations.Algorithmic using (κ; t-sub; not-t-sub)
import Surface.Derivations.Declarative as D
import Surface.Derivations.Declarative.Theorems.Agreement as D
open import Surface.Derivations.Common

as-sub' : Γ A.⊢[ θ , E ] τ' <: τ
        → ∃[ κ ] (Γ A.⊢[ θ , E of κ ] ε ⦂ τ')
        → Γ A.⊢[ θ , E of t-sub ] ε ⦂ τ
as-sub' <:δ ⟨ t-sub , A.T-Sub εδ τδ <:'δ ⟩ = A.T-Sub εδ (A.Γ⊢τ'<:τ-⇒-Γ⊢τ <:δ) {! !}
as-sub' <:δ ⟨ not-t-sub , εδ ⟩ = A.T-Sub εδ (A.Γ⊢τ'<:τ-⇒-Γ⊢τ <:δ) <:δ

mutual
  from-Γ : Γ D.ok[ θ , E ]
         → Γ A.ok[ θ , E ]
  from-Γ D.TCTX-Empty = A.TCTX-Empty
  from-Γ (D.TCTX-Bind Γok τδ) = A.TCTX-Bind (from-Γ Γok) (from-τ τδ)

  from-τ : Γ D.⊢[ θ , E ] τ
         → Γ A.⊢[ θ , E ] τ
  from-τ (D.TWF-TrueRef Γok) = A.TWF-TrueRef (from-Γ Γok)
  from-τ (D.TWF-Base ε₁δ ε₂δ) = A.TWF-Base (A.as-sub (from-ε ε₁δ)) (A.as-sub (from-ε ε₂δ))
  from-τ (D.TWF-Conj τ₁δ τ₂δ) = A.TWF-Conj (from-τ τ₁δ) (from-τ τ₂δ)
  from-τ (D.TWF-Arr τ₁δ τ₂δ) = A.TWF-Arr (from-τ τ₁δ) (from-τ τ₂δ)
  from-τ (D.TWF-ADT consδs) = A.TWF-ADT (from-cons consδs)

  from-ε : Γ D.⊢[ θ , E ] ε ⦂ τ
         → ∃[ κ ] (Γ A.⊢[ θ , E of κ ] ε ⦂ τ)
  from-ε (D.T-Unit Γok) = ⟨ _ , A.T-Unit (from-Γ Γok) ⟩
  from-ε (D.T-Var Γok ∈) = ⟨ _ , A.T-Var (from-Γ Γok) ∈ ⟩
  from-ε (D.T-Abs arrδ εδ) with from-ε εδ
  ... | ⟨ not-t-sub , εδ' ⟩ = ⟨ _ , A.T-Abs (from-τ arrδ) εδ' ⟩
  ... | ⟨ t-sub , A.T-Sub εδ' τδ <:δ ⟩
        = let Γ⊢τ₁⇒τ' = A.Γ,τ₁⊢τ₂-⇒-Γ⊢τ₁⇒τ₂ (A.Γ⊢ε⦂τ-⇒-Γ⊢τ εδ')
              Γ⊢τ₁ = case Γ⊢τ₁⇒τ' of λ where (A.TWF-Arr τ₁δ _) → τ₁δ
           in ⟨ _ , A.T-Sub (A.T-Abs Γ⊢τ₁⇒τ' εδ') (from-τ arrδ) (A.Γ⊢τ'<:τ-⇒-Γ⊢τ₀⇒τ'<:τ₀⇒τ Γ⊢τ₁ <:δ) ⟩
  from-ε εδ@(D.T-App ε₁δ ε₂δ) with from-ε ε₁δ
  ... | ⟨ t-sub , A.T-Sub ε₁δ' τδ <:δ@(A.ST-Arr <:₁δ <:₂δ _ _) ⟩
        = let τ₂-subst-δ = {! !}
              τ₂'-subst-δ = {! !}
           in ⟨ _
              , A.T-Sub
                  (A.T-App ε₁δ' (as-sub' <:₁δ (from-ε ε₂δ)) refl τ₂'-subst-δ)
                  τ₂-subst-δ
                  {! !}
              ⟩
  ... | ⟨ not-t-sub , ε₁δ' ⟩
        = let τ₂-subst-δ = {! D.Γ⊢ε⦂τ-⇒-Γ⊢τ εδ!}
           in ⟨ _ , A.T-App ε₁δ' (A.as-sub (from-ε ε₂δ)) refl τ₂-subst-δ ⟩
  from-ε (D.T-Case resδ εδ branches-well-typed) = {! !}
  from-ε (D.T-Con ≡-prf εδ adtτ) = {! !}
  from-ε (D.T-Sub εδ τδ <:δ) with Σεδ@(⟨ _ , εδ' ⟩) ← from-ε εδ = ⟨ _ , as-sub' (from-<: (A.Γ⊢ε⦂τ-⇒-Γ⊢τ εδ') (from-τ τδ) <:δ) Σεδ ⟩

  from-<: : Γ A.⊢[ θ , E ] τ'
          → Γ A.⊢[ θ , E ] τ
          → Γ D.⊢[ θ , E ] τ' <: τ
          → Γ A.⊢[ θ , E ] τ' <: τ
  from-<: τ'δ τδ (D.ST-Base is-just) = A.ST-Base is-just (enriched τ'δ) (enriched τδ)
  from-<: τ'δ@(A.TWF-Arr τ₁δ τ₂'δ) τδ@(A.TWF-Arr τ₁'δ τ₂δ) (D.ST-Arr <:₁δ <:₂δ x y)
    = A.ST-Arr
        (from-<: τ₁'δ τ₁δ <:₁δ)
        (from-<: {! !} τ₂δ <:₂δ)
        (enriched τ'δ)
        (enriched τδ)

  from-cons : {adtCons : ADTCons nₐ ℓ}
            → All (Γ D.⊢[ θ , E ]_) adtCons
            → All (Γ A.⊢[ θ , E ]_) adtCons
  from-cons [] = []
  from-cons (δ ∷ δs) = from-τ δ ∷ from-cons δs
