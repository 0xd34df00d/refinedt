{-# OPTIONS --safe #-}

module Surface.Safety where

open import Data.Fin using (zero; suc)
open import Data.Nat using (zero)
open import Data.Vec.Base using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.WellScoped
open import Surface.WellScoped.CtxSuffix
open import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.Substitution as S
open import Surface.WellScoped.Substitution.Stable
open import Surface.Derivations
open import Surface.Operational
open import Surface.Operational.BetaEquivalence
open import Surface.Operational.Lemmas
open import Surface.Theorems.SubstTyping
open import Surface.Theorems.Subtyping

data Canonical : STerm ℓ → SType ℓ → Set where
  C-Unit : Canonical (SUnit {ℓ}) ⟨ BUnit ∣ Τ ⟩
  C-Lam  : Canonical (SLam τ ε) (τ₁ ⇒ τ₂)
  C-Con  : ∀ {cons : ADTCons (Mkℕₐ (suc n)) zero}
         → (scrut-canonical : Canonical ε τ)
         → Canonical (SCon idx ε cons) (⊍ cons)

canonical-<: : ⊘ ⊢ τ <: τ'
             → Canonical ε τ
             → Canonical ε τ'
canonical-<: (ST-Base oracle is-just) C-Unit rewrite Oracle.⇒-consistent oracle is-just = C-Unit
canonical-<: (ST-Arr _ _) C-Lam = C-Lam

canonical : ⊘ ⊢ ε ⦂ τ
          → IsValue ε
          → Canonical ε τ
canonical (T-Var _ _) ()
canonical (T-App _ _) ()
canonical (T-Case _ _ _) ()
canonical (T-Unit Γok) IV-Unit = C-Unit
canonical (T-Abs arrδ εδ) IV-Abs = C-Lam
canonical (T-Con _ εδ adtτ) (IV-ADT is-value) = C-Con (canonical εδ is-value)
canonical (T-Sub εδ Γ⊢τ' <:) is-value = canonical-<: <: (canonical εδ is-value)

data Progress (ε : STerm ℓ) : Set where
  step : (ε↝ε' : ε ↝ ε')
       → Progress ε
  done : (is-value : IsValue ε)
       → Progress ε

progress : ⊘ ⊢ ε ⦂ τ
         → Progress ε
progress (T-Unit Γok) = done IV-Unit
progress (T-Abs arrδ εδ) = done IV-Abs
progress (T-App {ε₂ = ε₂} εδ₁ εδ₂) with progress εδ₁
... | step ε↝ε' = step (E-AppL ε↝ε')
... | done is-value-ε₁ with progress εδ₂
...   | step ε↝ε' = step (E-AppR is-value-ε₁ ε↝ε')
...   | done is-value-ε₂ with canonical εδ₁ is-value-ε₁
...     | C-Lam = step (E-AppAbs is-value-ε₂)
progress (T-Case resδ εδ branches) with progress εδ
... | step ε↝ε' = step (E-CaseScrut ε↝ε')
... | done is-value with canonical εδ is-value
...   | C-Con scrut-canonical with is-value
...     | IV-ADT ε-value = step (E-CaseMatch ε-value _)
progress (T-Con _ εδ adtτ) with progress εδ
... | step ε↝ε' = step (E-ADT ε↝ε')
... | done is-value = done (IV-ADT is-value)
progress (T-Sub εδ τδ τ<:τ') = progress εδ
progress (T-RConv εδ τ↝τ') = progress εδ


SLam-inv : Γ ⊢ SLam τ ε ⦂ τ₁ ⇒ τ₂
         → Γ , τ₁ ⊢ ε ⦂ τ₂
SLam-inv (T-Abs _ εδ) = εδ
SLam-inv (T-Sub εδ (TWF-Arr τ₁-ok τ₂-ok₁) (ST-Arr <:₁ <:₂)) = T-Sub (Γ⊢ε⦂τ-narrowing ⊘ <:₁ τ₁-ok (SLam-inv εδ)) τ₂-ok₁ <:₂

preservation : ε ↝ ε'
             → Γ ⊢ ε ⦂ τ
             → Γ ⊢ ε' ⦂ τ
preservation ε↝ε' (T-Sub εδ Γ⊢τ' Γ⊢τ<:τ') = T-Sub (preservation ε↝ε' εδ) Γ⊢τ' Γ⊢τ<:τ'
preservation ε↝ε' (T-RConv εδ τ↝τ') = T-RConv (preservation ε↝ε' εδ) τ↝τ'
preservation (E-AppL ε↝ε') (T-App εδ₁ εδ₂) = T-App (preservation ε↝ε' εδ₁) εδ₂
preservation (E-AppR x ε↝ε') (T-App εδ₁ εδ₂) = T-RConv (T-App εδ₁ (preservation ε↝ε' εδ₂)) (≡rβ-Subst _ _ _ ε↝ε')
preservation (E-AppAbs ε₂-is-value) (T-App εδ₁ εδ₂) = sub-Γ⊢ε⦂τ-front εδ₂ (SLam-inv εδ₁)
preservation (E-ADT ε↝ε') (T-Con ≡-prf εδ adtτ) = T-Con ≡-prf (preservation ε↝ε' εδ) adtτ
preservation (E-CaseScrut ε↝ε') (T-Case resδ εδ branches) = T-Case resδ (preservation ε↝ε' εδ) branches
preservation (E-CaseMatch ε-is-value idx) (T-Case resδ εδ branches) =
  let branchδ = sub-Γ⊢ε⦂τ-front (con-has-type εδ) (branch-has-type idx branches)
   in subst-Γ⊢ε⦂τ-τ (replace-weakened-τ-zero _ _) branchδ
  where
    branch-has-type : ∀ {cons : ADTCons (Mkℕₐ n) ℓ} {bs : CaseBranches (Mkℕₐ n) ℓ} {τ}
                    → (idx : Fin n)
                    → BranchesHaveType Γ cons bs τ
                    → Γ , lookup cons idx ⊢ CaseBranch.body (lookup bs idx) ⦂ R.weaken-τ τ
    branch-has-type zero (OneMoreBranch εδ bht) = εδ
    branch-has-type (suc idx) (OneMoreBranch εδ bht) = branch-has-type idx bht

    con-has-type : ∀ {cons cons' : ADTCons (Mkℕₐ (suc n)) ℓ} {idx}
                 → Γ ⊢ SCon idx ε cons ⦂ ⊍ cons'
                 → Γ ⊢ ε ⦂ lookup cons' idx
    con-has-type (T-Con refl conδ adtτ) = conδ
