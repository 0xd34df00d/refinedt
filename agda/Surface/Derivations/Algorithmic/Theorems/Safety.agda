{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Safety where

open import Data.Fin using (zero; suc)
open import Data.Nat using (zero)
open import Data.Vec.Base using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.Renaming as R
open import Surface.Syntax.Substitution.Stable
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Agreement
open import Surface.Derivations.Algorithmic.Theorems.Helpers
open import Surface.Operational
open import Surface.Derivations.Algorithmic.Theorems.Safety.Helpers

data Progress (ε : STerm ℓ) : Set where
  step : (ε↝ε' : ε ↝ ε')
       → Progress ε
  done : (is-value : IsValue ε)
       → Progress ε

progress : ⊘ ⊢[ θ , φ of κ ] ε ⦂ τ
         → Progress ε
progress (T-Unit _) = done IV-Unit
progress (T-Abs _) = done IV-Abs
progress (T-App ε₁δ ε₂δ _ _) with progress ε₁δ
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
progress (T-Sub εδ _ _) = progress εδ
