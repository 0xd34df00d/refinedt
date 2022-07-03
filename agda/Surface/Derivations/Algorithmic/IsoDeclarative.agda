module Surface.Derivations.Algorithmic.IsoDeclarative where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.Actions
open import Surface.Syntax.Renaming
open import Surface.Syntax.Substitution

import Surface.Derivations.Algorithmic as A
import Surface.Derivations.Algorithmic.Theorems.Agreement as A
open import Surface.Derivations.Algorithmic using (κ; t-sub; not-t-sub)
import Surface.Derivations.Declarative as D
import Surface.Derivations.Declarative.Theorems.Agreement as D
open import Surface.Derivations.Common

to-sub : ∃[ κ ] (Γ A.⊢[ θ , E of κ ] ε ⦂ τ)
       → Γ A.⊢[ θ , E of t-sub ] ε ⦂ τ
to-sub ⟨ t-sub , εδ ⟩ = εδ
to-sub ⟨ not-t-sub , εδ ⟩ = A.T-Sub εδ {! !} {! !}

mutual
  from-Γ : Γ D.ok[ θ , E ]
         → Γ A.ok[ θ , E ]
  from-Γ D.TCTX-Empty = A.TCTX-Empty
  from-Γ (D.TCTX-Bind Γok τδ) = A.TCTX-Bind (from-Γ Γok) (from-τ τδ)

  from-τ : Γ D.⊢[ θ , E ] τ
         → Γ A.⊢[ θ , E ] τ
  from-τ (D.TWF-TrueRef Γok) = A.TWF-TrueRef (from-Γ Γok)
  from-τ (D.TWF-Base ε₁δ ε₂δ) = A.TWF-Base (to-sub (from-ε ε₁δ)) (to-sub (from-ε ε₂δ))
  from-τ (D.TWF-Conj τ₁δ τ₂δ) = A.TWF-Conj (from-τ τ₁δ) (from-τ τ₂δ)
  from-τ (D.TWF-Arr τ₁δ τ₂δ) = {! !}
  from-τ (D.TWF-ADT consδs) = {! !}

  from-ε : Γ D.⊢[ θ , E ] ε ⦂ τ
         → ∃[ κ ] (Γ A.⊢[ θ , E of κ ] ε ⦂ τ)
  from-ε (D.T-Unit Γok) = ⟨ _ , A.T-Unit (from-Γ Γok) ⟩
  from-ε (D.T-Var Γok ∈) = ⟨ _ , A.T-Var (from-Γ Γok) ∈ ⟩
  from-ε (D.T-Abs arrδ εδ) with from-ε εδ
  ... | ⟨ not-t-sub , εδ' ⟩ = ⟨ _ , A.T-Abs (from-τ arrδ) εδ' ⟩
  ... | ⟨ t-sub , A.T-Sub εδ' τδ <:δ ⟩
        = let Γ,τ₁⊢τ' = A.Γ⊢ε⦂τ-⇒-Γ⊢τ εδ'
              Γ,τ₁-ok = A.Γ⊢ε⦂τ-⇒-Γok εδ'
              Γ⊢τ₁⇒τ' = A.TWF-Arr (case Γ,τ₁-ok of λ where (A.TCTX-Bind _ τ₁δ) → τ₁δ) Γ,τ₁⊢τ'
           in ⟨ _ , A.T-Sub (A.T-Abs Γ⊢τ₁⇒τ' εδ') (from-τ arrδ) {! !} ⟩
  from-ε εδ@(D.T-App ε₁δ ε₂δ) with from-ε ε₁δ
  ... | ⟨ t-sub , A.T-Sub ε₁δ' τδ <:δ@(A.ST-Arr _ _ _ _) ⟩ = ⟨ _ , A.T-Sub (A.T-App ε₁δ' {! !} refl {! !}) {! !} {! !} ⟩
  ... | ⟨ not-t-sub , ε₁δ' ⟩ = ⟨ _ , A.T-App ε₁δ' (to-sub (from-ε ε₂δ)) refl {! D.Γ⊢ε⦂τ-⇒-Γ⊢τ εδ !} ⟩
  from-ε (D.T-Case resδ εδ branches-well-typed) = {! !}
  from-ε (D.T-Con ≡-prf εδ adtτ) = {! !}
  from-ε (D.T-Sub εδ τ'δ <:) = {! !}
