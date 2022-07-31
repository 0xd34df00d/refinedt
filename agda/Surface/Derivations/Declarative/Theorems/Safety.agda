{-# OPTIONS --safe #-}

module Surface.Derivations.Declarative.Theorems.Safety where

open import Data.Fin using (zero; suc)
open import Data.Nat using (zero)
open import Data.Vec.Base using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.Renaming as R
open import Surface.Syntax.Substitution.Stable
open import Surface.Derivations.Declarative
open import Surface.Derivations.Declarative.Theorems.Agreement
open import Surface.Derivations.Declarative.Theorems.Substitution
open import Surface.Derivations.Declarative.Theorems.Helpers
open import Surface.Operational

open import Surface.Derivations.Declarative.Theorems.Safety.Helpers

data Progress (ε : STerm ℓ) : Set where
  step : (ε↝ε' : ε ↝ ε')
       → Progress ε
  done : (is-value : IsValue ε)
       → Progress ε

progress : ⊘ ⊢[ θ ] ε ⦂ τ
         → Progress ε
progress (T-Unit _) = done IV-Unit
progress (T-Abs _ _) = done IV-Abs
progress (T-App ε₁δ ε₂δ) with progress ε₁δ
... | step ε↝ε' = step (E-AppL ε↝ε')
... | done is-value-ε₁ with canonical-⇒ ε₁δ is-value-ε₁ refl
...   | C-Lam = step E-AppAbs
progress (T-Case _ εδ _) with progress εδ
... | step ε↝ε' = step (E-CaseScrut ε↝ε')
... | done is-value with canonical-⊍ εδ is-value refl
...   | C-Con with is-value
...     | IV-ADT ε-value = step (E-CaseMatch ε-value _)
progress (T-Con _ εδ _) with progress εδ
... | step ε↝ε' = step (E-ADT ε↝ε')
... | done is-value = done (IV-ADT is-value)
progress (T-Sub εδ _ _) = progress εδ


preservation : ε ↝ ε'
             → Γ ⊢[ θ ] ε ⦂ τ
             → Γ ⊢[ θ ] ε' ⦂ τ
preservation ε↝ε' (T-Sub εδ Γ⊢τ' Γ⊢τ<:τ') = T-Sub (preservation ε↝ε' εδ) Γ⊢τ' Γ⊢τ<:τ'
preservation (E-AppL ε↝ε') (T-App ε₁δ ε₂δ) = T-App (preservation ε↝ε' ε₁δ) ε₂δ
preservation (E-AppAbs) (T-App ε₁δ ε₂δ) = sub-Γ⊢ε⦂τ-front ε₂δ (SLam-inv ε₁δ)
preservation (E-ADT ε↝ε') (T-Con ≡-prf εδ adtτ) = T-Con ≡-prf (preservation ε↝ε' εδ) adtτ
preservation (E-CaseScrut ε↝ε') (T-Case resδ εδ branches) = T-Case resδ (preservation ε↝ε' εδ) branches
preservation (E-CaseMatch ε-is-value ι) (T-Case resδ εδ branches)
  = let branchδ = sub-Γ⊢ε⦂τ-front (con-has-type εδ) (branch-has-type ι branches)
     in subst-Γ⊢ε⦂τ-τ (replace-weakened-τ-zero _ _) branchδ
  where
  branch-has-type : ∀ {cons : ADTCons (Mkℕₐ n) ℓ} {bs : CaseBranches (Mkℕₐ n) ℓ} {τ}
                  → (ι : Fin n)
                  → BranchesHaveType θ Γ cons bs τ
                  → Γ , lookup cons ι ⊢[ θ ] CaseBranch.body (lookup bs ι) ⦂ R.weaken-τ τ
  branch-has-type zero (OneMoreBranch εδ _) = εδ
  branch-has-type (suc ι) (OneMoreBranch _ bht) = branch-has-type ι bht
