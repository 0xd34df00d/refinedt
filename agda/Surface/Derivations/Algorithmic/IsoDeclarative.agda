module Surface.Derivations.Algorithmic.IsoDeclarative where

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

mutual
  from-Γ : Γ D.ok[ θ , E ]
         → Γ A.ok[ θ , E ]
  from-Γ D.TCTX-Empty = A.TCTX-Empty
  from-Γ (D.TCTX-Bind Γok τδ) = A.TCTX-Bind (from-Γ Γok) (from-τ τδ)

  from-τ : Γ D.⊢[ θ , E ] τ
         → Γ A.⊢[ θ , E ] τ
  from-τ (D.TWF-TrueRef Γok) = A.TWF-TrueRef (from-Γ Γok)
  from-τ (D.TWF-Base ε₁δ ε₂δ) = A.TWF-Base (from-ε ε₁δ) (from-ε ε₂δ)
  from-τ (D.TWF-Conj τ₁δ τ₂δ) = A.TWF-Conj (from-τ τ₁δ) (from-τ τ₂δ)
  from-τ (D.TWF-Arr τ₁δ τ₂δ) = A.TWF-Arr (from-τ τ₁δ) (from-τ τ₂δ)
  from-τ (D.TWF-ADT consδs) = A.TWF-ADT (from-cons consδs)

  from-ε : Γ D.⊢[ θ , E ] ε ⦂ τ
         → Γ A.⊢[ θ , E of t-sub ] ε ⦂ τ
  from-ε (D.T-Unit Γok) = A.as-sub (A.T-Unit (from-Γ Γok))
  from-ε (D.T-Var Γok ∈) = A.as-sub (A.T-Var (from-Γ Γok) ∈)
  from-ε (D.T-Abs arrδ εδ)
    with A.T-Sub εδ' <:δ ← from-ε εδ
       = let Γ⊢τ₁⇒τ' = A.Γ,τ₁⊢τ₂-⇒-Γ⊢τ₁⇒τ₂ (A.Γ⊢ε⦂τ-⇒-Γ⊢τ εδ')
             Γ⊢τ₁ = case Γ⊢τ₁⇒τ' of λ where (A.TWF-Arr τ₁δ _) → τ₁δ
          in A.T-Sub (A.T-Abs εδ') (A.Γ⊢τ'<:τ-⇒-Γ⊢τ₀⇒τ'<:τ₀⇒τ <:δ)
  from-ε εδ@(D.T-App ε₁δ ε₂δ)
    with A.T-Sub ε₁δ' <:δ@(A.ST-Arr <:₁δ <:₂δ) ← from-ε ε₁δ
        = let τ₂-subst-δ = {! !}
              τ₂'-subst-δ = {! !}
           in A.T-Sub
                (A.T-App ε₁δ' {! (A.as-sub' <:₁δ (from-ε ε₂δ)) !} refl)
                τ₂-subst-δ
              {-
  ... | ⟨ not-t-sub , ε₁δ' ⟩
        = let τ₂-subst-δ = {! D.Γ⊢ε⦂τ-⇒-Γ⊢τ εδ!}
           in ⟨ _ , A.T-App ε₁δ' (A.as-sub (from-ε ε₂δ)) refl τ₂-subst-δ ⟩
           -}
  from-ε (D.T-Case resδ εδ branches-well-typed) = {! !}
  from-ε (D.T-Con ≡-prf εδ adtτ) = {! !}
  from-ε (D.T-Sub εδ τδ <:δ) with εδ' ← from-ε εδ = {! A.as-sub' (from-<: (A.Γ⊢ε⦂τ-⇒-Γ⊢τ εδ') (from-τ τδ) <:δ) Σεδ !}

  from-<: : Γ D.⊢[ θ , E ] τ' <: τ
          → Γ A.⊢[ θ ] τ' <: τ
  from-<: (D.ST-Base is-just) = A.ST-Base is-just
  from-<: (D.ST-Arr <:₁δ <:₂δ _ _) = A.ST-Arr (from-<: <:₁δ) (from-<: <:₂δ)

  from-cons : {adtCons : ADTCons nₐ ℓ}
            → All (Γ D.⊢[ θ , E ]_) adtCons
            → All (Γ A.⊢[ θ , E ]_) adtCons
  from-cons [] = []
  from-cons (δ ∷ δs) = from-τ δ ∷ from-cons δs
