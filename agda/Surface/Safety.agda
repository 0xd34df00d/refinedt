{-# OPTIONS --safe #-}

module Surface.Safety where

open import Data.Nat using (zero)

open import Surface.WellScoped
open import Surface.Derivations
open import Surface.Operational

data Canonical : STerm ℓ → SType ℓ → Set where
  C-Unit : Canonical (SUnit {ℓ}) ⟨ BUnit ∣ Τ ⟩
  C-Lam  : ⊘ ⊢ SLam τ₁ ε ⦂ τ₁ ⇒ τ₂
         → Canonical (SLam τ ε) (τ₁ ⇒ τ₂)
  C-Con  : ∀ {cons : ADTCons (Mkℕₐ (suc n)) zero}
         → ⊘ ⊢ SCon idx ε cons ⦂ ⊍ cons
         → Canonical ε τ
         → Canonical (SCon idx ε cons) (⊍ cons)

canonical : ⊘ ⊢ ε ⦂ τ
          → IsValue ε
          → Canonical ε τ
canonical (T-Var _ _) ()
canonical (T-App _ _) ()
canonical (T-Case _ _ _) ()
canonical (T-Unit Γok) IV-Unit = C-Unit
canonical (T-Abs arrδ εδ) IV-Abs = C-Lam (T-Abs arrδ εδ)
canonical (T-Con εδ adtτ) (IV-ADT is-value) = C-Con (T-Con εδ adtτ) (canonical εδ is-value)
canonical (T-Sub εδ Γ⊢τ' <:) IV-Unit = {! !}
canonical (T-Sub εδ Γ⊢τ' <:) IV-Abs = {! !}
canonical (T-Sub εδ Γ⊢τ' <:) (IV-ADT is-value) = {! !}


data Progress (ε : STerm ℓ) : Set where
  step : ∀ ε'
       → (ε↝ε' : ε ↝ ε')
       → Progress ε
  done : (is-value : IsValue ε)
       → Progress ε

progress : ⊘ ⊢ ε ⦂ τ
         → Progress ε
progress (T-Unit Γok) = done IV-Unit
progress (T-Abs arrδ εδ) = done IV-Abs
progress (T-App εδ₁ εδ₂) with progress εδ₁
... | step ε' ε↝ε' = step (SApp ε' _) (E-AppL ε↝ε')
... | done is-value with progress εδ₂
...   | step ε' ε↝ε' = step (SApp _ ε') (E-AppR is-value ε↝ε')
...   | done is-value₁ = {! !}
progress (T-Case resδ εδ branches) with progress εδ
... | step ε' ε↝ε' = step (SCase ε' _) (E-CaseScrut ε↝ε')
... | done is-value = {! !}
progress (T-Con εδ adtτ) = {! !}
progress (T-Sub εδ τδ τ<:τ') = progress εδ
