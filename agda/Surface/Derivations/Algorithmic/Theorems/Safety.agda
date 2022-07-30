{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Safety where

open import Data.Fin using (zero; suc)
open import Data.Nat using (zero)
open import Data.Vec.Base using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.Renaming as R
open import Surface.Syntax.Substitution as S
open import Surface.Syntax.Substitution.Stable
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Agreement
open import Surface.Derivations.Algorithmic.Theorems.Safety.Helpers
open import Surface.Derivations.Algorithmic.Theorems.Substitution
open import Surface.Derivations.Algorithmic.Theorems.Subtyping
open import Surface.Derivations.Algorithmic.Theorems.Helpers
open import Surface.Operational

data Progress (ε : STerm ℓ) : Set where
  step : (ε↝ε' : ε ↝ ε')
       → Progress ε
  done : (is-value : IsValue ε)
       → Progress ε

progress : ⊘ ⊢[ θ , φ of κ ] ε ⦂ τ
         → Progress ε
progress (T-Unit _) = done IV-Unit
progress (T-Abs _) = done IV-Abs
progress (T-App ε₁δ ε₂δ _) with progress ε₁δ
... | step ε↝ε' = step (E-AppL ε↝ε')
... | done is-value-ε₁
        with C-Lam ← canonical-⇒ ε₁δ is-value-ε₁ refl
           = step E-AppAbs
progress (T-Case _ εδ _) with progress εδ
... | step ε↝ε' = step (E-CaseScrut ε↝ε')
... | done is-value-ε
        with C-Con ← canonical-⊍ εδ is-value-ε refl
           | IV-ADT ε-value ← is-value-ε
           = step (E-CaseMatch ε-value _)
progress (T-Con _ εδ _) with progress εδ
... | step ε↝ε' = step (E-ADT ε↝ε')
... | done is-value = done (IV-ADT is-value)
progress (T-Sub εδ _) = progress εδ


preservation : ε ↝ ε'
             → Γ ⊢[ θ , φ of κ ] ε ⦂ τ
             → Γ ⊢[ θ , φ of t-sub ] ε' ⦂ τ
preservation ε↝ε' (T-Sub εδ <:δ) = trans-sub <:δ (preservation ε↝ε' εδ)
preservation (E-AppL ε↝ε') (T-App {τ₁ = τ₁'} {τ₂ = τ₂} ε₁δ ε₂δ refl)
  with T-Sub {τ' = τ₁ ⇒ τ₂'} ε₁δ' <:δ@(ST-Arr <:₁δ <:₂δ) ← preservation ε↝ε' ε₁δ
     = T-Sub (T-App ε₁δ' (trans-sub <:₁δ ε₂δ) refl) (sub-Γ⊢τ'<:τ-front ε₂δ <:₂δ)
preservation E-AppAbs (T-App (T-Abs ε₁-bodyδ) ε₂δ refl) = sub-Γ⊢ε⦂τ-front ε₂δ ε₁-bodyδ
preservation (E-ADT ε↝ε') (T-Con ≡-prf εδ adtτ) = {! !}
preservation (E-CaseScrut ε↝ε') (T-Case resδ εδ bsδ) = {! !}
preservation (E-CaseMatch x ι) (T-Case resδ εδ bsδ) = {! !}
