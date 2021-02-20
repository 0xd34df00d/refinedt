{-# OPTIONS --safe #-}

module Common.Helpers where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Fin.Extra

infix 2 _f≡_
_f≡_ : ∀ {A B : Set} (f₁ f₂ : A → B) → Set
f₁ f≡ f₂ = ∀ x → f₁ x ≡ f₂ x

replace-at-generic : {TermTy : ℕ → Set}
                   → (MkVar : ∀ {ℓ} → Fin ℓ → TermTy ℓ)
                   → ∀ {ℓ} → Fin (suc ℓ) → TermTy ℓ → Fin (suc ℓ) → TermTy ℓ
replace-at-generic MkVar replace-idx ε var-idx with replace-idx <>? var-idx
-- replacement index is less than current variable index, so the variable points to a binder that just got closer to it,
-- so decrement the variable index:
... | less rep<var = MkVar (m<n-n-pred rep<var)
-- just replace the current variable with the term:
... | equal m≡n = ε
-- replacement index is greater than current variable index, so the variable still refers to the same binder,
-- so leave the var index as-is, just shrinking the bound of Fin as the binders count just decremented:
... | greater rep>var = MkVar (tighten rep>var)
