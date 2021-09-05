{-# OPTIONS --safe #-}

module Surface.Safety where

open import Data.Fin using (zero; suc)
open import Data.Nat using (zero)
open import Data.Product using (Σ; _×_; ∃; Σ-syntax; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Vec.Base using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.Renaming as R
open import Surface.Syntax.Substitution.Stable
open import Surface.Derivations
open import Surface.Operational
open import Surface.Theorems.Agreement
--open import Surface.Theorems.Substitution
open import Surface.Theorems.Helpers
open import Surface.Safety.Helpers

data Progress (ε : STerm ℓ) : Set where
  step : (ε↝ε' : ε ↝ ε')
       → Progress ε
  done : (is-value : IsValue ε)
       → Progress ε

progress : ⊘ ⊢[ φ ] ε ⦂ τ
         → Progress ε
progress (T-Unit Γok) = done IV-Unit
progress (T-Abs arrδ εδ) = done IV-Abs
progress (T-App {ε₂ = ε₂} ε₁δ ε₂δ _ _) with progress ε₁δ
... | step ε↝ε' = step (E-AppL ε↝ε')
... | done is-value-ε₁ with canonical-⇒ ε₁δ is-value-ε₁ refl
...   | C-Lam = step E-AppAbs
progress (T-Case resδ εδ branches) with progress εδ
... | step ε↝ε' = step (E-CaseScrut ε↝ε')
... | done is-value with canonical-⊍ εδ is-value refl
...   | C-Con with is-value
...     | IV-ADT ε-value = step (E-CaseMatch ε-value _)
progress (T-Con _ εδ adtτ) with progress εδ
... | step ε↝ε' = step (E-ADT ε↝ε')
... | done is-value = done (IV-ADT is-value)

preservation : ε ↝ ε'
             → Γ ⊢[ φ ] ε ⦂ τ
             → ∃[ τ' ] ((Γ ⊢[ φ ] τ' <: τ) × (Γ ⊢[ φ ] ε' ⦂ τ'))
preservation (E-AppL ε↝ε') (T-App ε₁δ ε₂δ <: resτδ) with preservation ε↝ε' ε₁δ
... | ⟨ τ' , ⟨ τ'<:τ@(ST-Arr _ _ _ _) , ε₁δ' ⟩ ⟩ = ⟨ {! !} , ⟨ {! !} , T-App ε₁δ' ε₂δ {! !} {! !} ⟩ ⟩
preservation E-AppAbs (T-App (T-Abs arrδ ε₁δ) ε₂δ <: resτδ) = {! !}
preservation (E-ADT ε↝ε') (T-Con ≡-prf εδ adtτ) = {! !}
preservation (E-CaseScrut ε↝ε') (T-Case resδ εδ branches) = {! !}
preservation (E-CaseMatch ε-is-value ι) (T-Case resδ εδ branches) = {! !}

{-
preservation : ε ↝ ε'
             → Γ ⊢[ φ ] ε ⦂ τ
             → Γ ⊢[ φ ] ε' ⦂ τ
preservation (E-AppL ε↝ε') (T-App ε₁δ ε₂δ <: resτδ) = T-App (preservation ε↝ε' ε₁δ) ε₂δ <: resτδ
preservation (E-AppAbs) (T-App ε₁δ ε₂δ <: resτδ) = {! !} -- sub-Γ⊢ε⦂τ-front ε₂δ (SLam-inv ε₁δ)
preservation (E-ADT ε↝ε') (T-Con ≡-prf εδ adtτ) = T-Con ≡-prf (preservation ε↝ε' εδ) adtτ
preservation (E-CaseScrut ε↝ε') (T-Case resδ εδ branches) = T-Case resδ (preservation ε↝ε' εδ) branches
preservation {φ = φ} (E-CaseMatch ε-is-value ι) (T-Case resδ εδ branches)
  = let branchδ = {! !} -- sub-Γ⊢ε⦂τ-front (con-has-type εδ) (branch-has-type ι branches)
     in subst-Γ⊢ε⦂τ-τ (replace-weakened-τ-zero _ _) branchδ
  where
  branch-has-type : ∀ {cons : ADTCons (Mkℕₐ n) ℓ} {bs : CaseBranches (Mkℕₐ n) ℓ} {τ}
                  → (ι : Fin n)
                  → BranchesHaveType φ Γ cons bs τ
                  → Γ , lookup cons ι ⊢[ φ ] CaseBranch.body (lookup bs ι) ⦂ R.weaken-τ τ
  branch-has-type zero (OneMoreBranch εδ _) = εδ
  branch-has-type (suc ι) (OneMoreBranch _ bht) = branch-has-type ι bht
  -}
