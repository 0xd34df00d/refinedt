{-# OPTIONS --safe #-}

module Surface.Safety where

open import Data.Empty
open import Data.Fin using (zero; suc)
open import Data.Nat using (zero)
open import Data.Vec.Base using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Renaming as R
open import Surface.Syntax.Substitution as S
open import Surface.Syntax.Substitution.Stable
open import Surface.Syntax.Shape
open import Surface.Derivations
open import Surface.Operational
open import Surface.Operational.BetaEquivalence
open import Surface.Operational.Lemmas
open import Surface.Theorems.Agreement
open import Surface.Theorems.Substitution
open import Surface.Theorems.Subtyping
open import Surface.Theorems.Helpers
open import Surface.Theorems.Γ-Equivalence

data Canonical : STerm ℓ → SType ℓ → Set where
  C-Lam  : Canonical (SLam τ ε) (τ₁ ⇒ τ₂)
  C-Con  : ∀ {cons cons' : ADTCons (Mkℕₐ (suc n)) zero}
         → Canonical (SCon ι ε cons) (⊍ cons')

canonical-⇒ : ⊘ ⊢ ε ⦂ τ
            → IsValue ε
            → τ ≡ τ₁ ⇒ τ₂
            → Canonical ε τ
canonical-⇒ (T-Abs arrδ εδ) is-value ≡-prf = C-Lam
canonical-⇒ (T-Sub εδ τ'δ <:@(ST-Arr _ _)) is-value refl with canonical-⇒ εδ is-value refl
... | C-Lam = C-Lam
canonical-⇒ (T-RConv {τ = τ₁' ⇒ τ₂'} εδ τ'δ τ~τ') is-value refl with canonical-⇒ εδ is-value refl
... | C-Lam = C-Lam
canonical-⇒ (T-RConv {τ = ⟨ _ ∣ _ ⟩} εδ τ'δ τ~τ') is-value refl = shape-⊥-elim ↭βτ-preserves-shape τ~τ' (λ ())
canonical-⇒ (T-RConv {τ = ⊍ _} εδ τ'δ τ~τ')       is-value refl = shape-⊥-elim ↭βτ-preserves-shape τ~τ' (λ ())

canonical-⊍ : {cons : ADTCons (Mkℕₐ n) zero}
            → ⊘ ⊢ ε ⦂ τ
            → IsValue ε
            → τ ≡ ⊍ cons
            → Canonical ε τ
canonical-⊍ (T-Con ≡-prf₁ εδ adtτ) (IV-ADT is-value) ≡-prf = C-Con
canonical-⊍ (T-Sub εδ τ'δ ()) _ refl
canonical-⊍ (T-RConv {τ = ⊍ cons} εδ τ'δ τ~τ') is-value refl with canonical-⊍ εδ is-value refl | ↭βτ-cons-same-length τ~τ'
... | C-Con | refl = C-Con
canonical-⊍ (T-RConv {τ = ⟨ _ ∣ _ ⟩} εδ τ'δ τ~τ') is-value refl = shape-⊥-elim ↭βτ-preserves-shape τ~τ' (λ ())
canonical-⊍ (T-RConv {τ = _ ⇒ _} εδ τ'δ τ~τ')     is-value refl = shape-⊥-elim ↭βτ-preserves-shape τ~τ' (λ ())

data Progress (ε : STerm ℓ) : Set where
  step : (ε↝ε' : ε ↝ ε')
       → Progress ε
  done : (is-value : IsValue ε)
       → Progress ε

progress : ⊘ ⊢ ε ⦂ τ
         → Progress ε
progress (T-Unit Γok) = done IV-Unit
progress (T-Abs arrδ εδ) = done IV-Abs
progress (T-App {ε₂ = ε₂} ε₁δ ε₂δ) with progress ε₁δ
... | step ε↝ε' = step (E-AppL ε↝ε')
... | done is-value-ε₁ with progress ε₂δ
...   | step ε↝ε' = step (E-AppR is-value-ε₁ ε↝ε')
...   | done is-value-ε₂ with canonical-⇒ ε₁δ is-value-ε₁ refl
...     | C-Lam = step (E-AppAbs is-value-ε₂)
progress (T-Case resδ εδ branches) with progress εδ
... | step ε↝ε' = step (E-CaseScrut ε↝ε')
... | done is-value with canonical-⊍ εδ is-value refl
...   | C-Con with is-value
...     | IV-ADT ε-value = step (E-CaseMatch ε-value _)
progress (T-Con _ εδ adtτ) with progress εδ
... | step ε↝ε' = step (E-ADT ε↝ε')
... | done is-value = done (IV-ADT is-value)
progress (T-Sub εδ τδ τ<:τ') = progress εδ
progress (T-RConv εδ _ τ↝τ') = progress εδ


SLam-inv : Γ ⊢ SLam τ ε ⦂ τ₁ ⇒ τ₂
         → Γ , τ₁ ⊢ ε ⦂ τ₂
SLam-inv (T-Abs _ εδ) = εδ
SLam-inv (T-Sub εδ (TWF-Arr τ₁-ok τ₂-ok₁) (ST-Arr <:₁ <:₂)) = T-Sub (Γ⊢ε⦂τ-narrowing ⊘ <:₁ τ₁-ok (SLam-inv εδ)) τ₂-ok₁ <:₂
SLam-inv (T-RConv {τ = τ₁' ⇒ τ₂'} εδ (TWF-Arr τ₁δ τ₂δ) τ~τ')
  = let Γ,τ₁⊢ε⦂τ₂' = Γ⊢ε⦂τ-equivalence ⊘ (↭βτ-⇒-dom τ~τ') τ₁δ (SLam-inv εδ)
     in T-RConv Γ,τ₁⊢ε⦂τ₂' τ₂δ (↭βτ-⇒-cod τ~τ')
SLam-inv (T-RConv {τ = ⟨ _ ∣ _ ⟩} εδ _ τ↝τ') = shape-⊥-elim ↭βτ-preserves-shape τ↝τ' λ ()
SLam-inv (T-RConv {τ = ⊍ _}       εδ _ τ↝τ') = shape-⊥-elim ↭βτ-preserves-shape τ↝τ' λ ()

lookup-preserves-Γ⊢τ : {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
                     → (ι : Fin (suc n))
                     → Γ ⊢ ⊍ cons
                     → Γ ⊢ lookup cons ι
lookup-preserves-Γ⊢τ ι (TWF-ADT consδs) = go ι consδs
  where
    go : (ι : Fin n)
       → {cons : ADTCons (Mkℕₐ n) ℓ}
       → All (Γ ⊢_) cons
       → Γ ⊢ lookup cons ι
    go zero (px ∷ _) = px
    go (suc ι) (_ ∷ consδs) = go ι consδs

con-has-type : ∀ {cons cons' : ADTCons (Mkℕₐ (suc n)) ℓ} {ι}
             → Γ ⊢ SCon ι ε cons ⦂ ⊍ cons'
             → Γ ⊢ ε ⦂ lookup cons' ι
con-has-type (T-Con refl conδ adtτ) = conδ
con-has-type (T-RConv {τ = ⟨ _ ∣ _ ⟩} εδ _ τ↝τ') = shape-⊥-elim ↭βτ-preserves-shape τ↝τ' λ ()
con-has-type (T-RConv {τ = _ ⇒ _}     εδ _ τ↝τ') = shape-⊥-elim ↭βτ-preserves-shape τ↝τ' λ ()
con-has-type (T-RConv {τ = ⊍ cons}    εδ τ'δ τ↝τ') with ↭βτ-cons-same-length τ↝τ'
... | refl = T-RConv (con-has-type εδ) (lookup-preserves-Γ⊢τ _ τ'δ) (↭βτ-lookup _ τ↝τ')

subst-Γ⊢ε⦂τ-τ : τ₁ ≡ τ₂
              → Γ ⊢ ε ⦂ τ₁
              → Γ ⊢ ε ⦂ τ₂
subst-Γ⊢ε⦂τ-τ refl εδ = εδ

preservation : ε ↝ ε'
             → Γ ⊢ ε ⦂ τ
             → Γ ⊢ ε' ⦂ τ
preservation ε↝ε' (T-Sub εδ Γ⊢τ' Γ⊢τ<:τ') = T-Sub (preservation ε↝ε' εδ) Γ⊢τ' Γ⊢τ<:τ'
preservation ε↝ε' (T-RConv εδ τ'δ τ↝τ') = T-RConv (preservation ε↝ε' εδ) τ'δ τ↝τ'
preservation (E-AppL ε↝ε') (T-App ε₁δ ε₂δ) = T-App (preservation ε↝ε' ε₁δ) ε₂δ
preservation (E-AppR x ε↝ε') (T-App ε₁δ ε₂δ)
  = let τ₂δ = arr-wf-⇒-cod-wf (Γ⊢ε⦂τ-⇒-Γ⊢τ ε₁δ)
        τ'δ = sub-Γ⊢τ-front ε₂δ τ₂δ
     in T-RConv (T-App ε₁δ (preservation ε↝ε' ε₂δ)) τ'δ (forward (↝βτ-Subst zero _ _ _ ε↝ε'))
preservation (E-AppAbs ε₂-is-value) (T-App ε₁δ ε₂δ) = sub-Γ⊢ε⦂τ-front ε₂δ (SLam-inv ε₁δ)
preservation (E-ADT ε↝ε') (T-Con ≡-prf εδ adtτ) = T-Con ≡-prf (preservation ε↝ε' εδ) adtτ
preservation (E-CaseScrut ε↝ε') (T-Case resδ εδ branches) = T-Case resδ (preservation ε↝ε' εδ) branches
preservation (E-CaseMatch ε-is-value ι) (T-Case resδ εδ branches)
  = let branchδ = sub-Γ⊢ε⦂τ-front (con-has-type εδ) (branch-has-type ι branches)
     in subst-Γ⊢ε⦂τ-τ (replace-weakened-τ-zero _ _) branchδ
  where
    branch-has-type : ∀ {cons : ADTCons (Mkℕₐ n) ℓ} {bs : CaseBranches (Mkℕₐ n) ℓ} {τ}
                    → (ι : Fin n)
                    → BranchesHaveType Γ cons bs τ
                    → Γ , lookup cons ι ⊢ CaseBranch.body (lookup bs ι) ⦂ R.weaken-τ τ
    branch-has-type zero (OneMoreBranch εδ bht) = εδ
    branch-has-type (suc ι) (OneMoreBranch εδ bht) = branch-has-type ι bht
