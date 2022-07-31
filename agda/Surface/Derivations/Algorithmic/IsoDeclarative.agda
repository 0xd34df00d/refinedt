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

module D-to-A where mutual
  map-Γ : Γ D.ok[ θ ]
        → Γ A.ok[ θ , M ]
  map-Γ D.TCTX-Empty = A.TCTX-Empty
  map-Γ (D.TCTX-Bind Γok τδ) = A.TCTX-Bind (map-Γ Γok) (map-τ τδ)

  map-τ : Γ D.⊢[ θ ] τ
        → Γ A.⊢[ θ , M ] τ
  map-τ (D.TWF-TrueRef Γok) = A.TWF-TrueRef (map-Γ Γok)
  map-τ (D.TWF-Base ε₁δ ε₂δ) = A.TWF-Base (map-ε ε₁δ) (map-ε ε₂δ)
  map-τ (D.TWF-Conj τ₁δ τ₂δ) = A.TWF-Conj (map-τ τ₁δ) (map-τ τ₂δ)
  map-τ (D.TWF-Arr τ₁δ τ₂δ) = A.TWF-Arr (map-τ τ₁δ) (map-τ τ₂δ)
  map-τ (D.TWF-ADT consδs) = A.TWF-ADT (map-cons consδs)

  map-ε : Γ D.⊢[ θ ] ε ⦂ τ
        → Γ A.⊢[ θ , M of t-sub ] ε ⦂ τ
  map-ε (D.T-Unit Γok) = A.as-sub (A.T-Unit (map-Γ Γok))
  map-ε (D.T-Var Γok ∈) = A.as-sub (A.T-Var (map-Γ Γok) ∈)
  map-ε (D.T-Abs arrδ εδ)
    with A.T-Sub εδ' <:δ ← map-ε εδ
       = let Γ⊢τ₁⇒τ' = A.Γ,τ₁⊢τ₂-⇒-Γ⊢τ₁⇒τ₂ (A.Γ⊢ε⦂τ-⇒-Γ⊢τ εδ')
             Γ⊢τ₁ = case Γ⊢τ₁⇒τ' of λ where (A.TWF-Arr τ₁δ _) → τ₁δ
          in A.T-Sub (A.T-Abs εδ') (A.Γ⊢τ'<:τ-⇒-Γ⊢τ₀⇒τ'<:τ₀⇒τ <:δ)
  map-ε (D.T-App ε₁δ ε₂δ)
    with A.T-Sub ε₁δ' (A.ST-Arr <:₁δ <:₂δ) ← map-ε ε₁δ
       = let ε₂δ' = map-ε ε₂δ
          in A.T-Sub
               (A.T-App ε₁δ' (A.trans-sub <:₁δ ε₂δ') refl)
               (A.sub-Γ⊢τ'<:τ-front ε₂δ' <:₂δ)
  map-ε (D.T-Case resδ εδ bsδ) = A.as-sub (A.T-Case (map-τ resδ) (map-ε εδ) (map-branches bsδ))
  map-ε (D.T-Con refl εδ adtτ)
    with A.T-Sub εδ' <:δ ← map-ε εδ
       = A.as-sub (A.T-Con <:δ εδ' (map-τ adtτ))
  map-ε (D.T-Sub εδ _ <:δ) = A.trans-sub (map-<: <:δ) (map-ε εδ)

  map-<: : Γ D.⊢[ θ ] τ' <: τ
         → Γ A.⊢[ θ ] τ' <: τ
  map-<: (D.ST-Base is-just) = A.ST-Base is-just
  map-<: (D.ST-Arr <:₁δ <:₂δ) = A.ST-Arr (map-<: <:₁δ) (map-<: <:₂δ)

  map-cons : {cons : ADTCons nₐ ℓ}
           → All (Γ D.⊢[ θ ]_) cons
           → All (Γ A.⊢[ θ , M ]_) cons
  map-cons [] = []
  map-cons (δ ∷ δs) = map-τ δ ∷ map-cons δs

  map-branches : {cons : ADTCons nₐ ℓ} {bs : CaseBranches nₐ ℓ}
               → D.BranchesHaveType θ Γ cons bs τ
               → A.BranchesHaveType θ M Γ cons bs τ
  map-branches D.NoBranches = A.NoBranches
  map-branches (D.OneMoreBranch εδ bsδ) = A.OneMoreBranch (map-ε εδ) (map-branches bsδ)

module A-to-D where mutual
  map-Γ : Γ A.ok[ θ , φ ]
        → Γ D.ok[ θ ]
  map-Γ A.TCTX-Empty = D.TCTX-Empty
  map-Γ (A.TCTX-Bind Γok τδ) = D.TCTX-Bind (map-Γ Γok) (map-τ τδ)

  map-τ : Γ A.⊢[ θ , φ ] τ
        → Γ D.⊢[ θ ] τ
  map-τ (A.TWF-TrueRef Γok) = D.TWF-TrueRef (map-Γ Γok)
  map-τ (A.TWF-Base ε₁δ ε₂δ) = D.TWF-Base (map-ε ε₁δ) (map-ε ε₂δ)
  map-τ (A.TWF-Conj τ₁δ τ₂δ) = D.TWF-Conj (map-τ τ₁δ) (map-τ τ₂δ)
  map-τ (A.TWF-Arr τ₁δ τ₂δ) = D.TWF-Arr (map-τ τ₁δ) (map-τ τ₂δ)
  map-τ (A.TWF-ADT consδs) = D.TWF-ADT (map-cons consδs)

  map-ε : Γ A.⊢[ θ , φ of κ ] ε ⦂ τ
        → Γ D.⊢[ θ ] ε ⦂ τ
  map-ε (A.T-Unit Γok) = {! !}
  map-ε (A.T-Var Γok x) = {! !}
  map-ε (A.T-Abs εδ) = {! !}
  map-ε (A.T-App εδ εδ₁ resτ-≡) = {! !}
  map-ε (A.T-Case resδ εδ bsδ) = {! !}
  map-ε (A.T-Con <:δ εδ adtτ) = {! !}
  map-ε (A.T-Sub εδ (A.ST-Base is-just)) = {! !}
  map-ε (A.T-Sub εδ (A.ST-Arr <:₁δ <:₂δ)) = {! !}
  map-ε (A.T-Sub εδ (A.ST-ADT cons-<:)) = {! !}

  map-cons : {cons : ADTCons nₐ ℓ}
           → All (Γ A.⊢[ θ , φ ]_) cons
           → All (Γ D.⊢[ θ ]_) cons
  map-cons [] = []
  map-cons (τδ ∷ consδs) = map-τ τδ ∷ map-cons consδs

  map-branches : {cons : ADTCons nₐ ℓ} {bs : CaseBranches nₐ ℓ}
               → A.BranchesHaveType θ φ Γ cons bs τ
               → D.BranchesHaveType θ Γ cons bs τ
  map-branches A.NoBranches = D.NoBranches
  map-branches (A.OneMoreBranch εδ bsδ) = D.OneMoreBranch (map-ε εδ) (map-branches bsδ)
