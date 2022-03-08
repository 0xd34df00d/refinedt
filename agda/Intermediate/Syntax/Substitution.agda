module Intermediate.Syntax.Substitution where

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Fin using (Fin; suc; zero; toℕ)
open import Data.Vec
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Common.Helpers
open import Data.Fin.Extra
open import Intermediate.Syntax
import      Intermediate.Syntax.Renaming as R
open import Intermediate.Syntax.Actions (record { Target = STerm
                                                ; var-action = λ ε → ε
                                                ; ext = λ where _ zero → SVar zero
                                                                σ (suc n) → R.weaken-ε (σ n)
                                                }
                                        ) public

replace-at : Fin (suc ℓ) → STerm ℓ → Fin (suc ℓ) → STerm ℓ
replace-at = replace-at-generic SVar

SubstOn : (ℕ → Set) → Set
SubstOn Ty = ∀ {ℓ} → Fin (suc ℓ) → STerm ℓ → Ty (suc ℓ) → Ty ℓ

infixr 6 [_↦τ_]_ [_↦ρ_]_ [_↦ε_]_ [_↦c_]_ [_↦bs_]_
[_↦τ_]_ : SubstOn SType
[_↦τ_]_ ι ε = act-τ (replace-at ι ε)

[_↦ρ_]_ : SubstOn Refinement
[_↦ρ_]_ ι ε = act-ρ (replace-at ι ε)

[_↦ε_]_ : SubstOn STerm
[_↦ε_]_ ι ε = act-ε (replace-at ι ε)

[_↦c_]_ : SubstOn (ADTCons nₐ)
[_↦c_]_ ι ε = act-cons (replace-at ι ε)

[_↦bs_]_ : SubstOn (CaseBranches nₐ)
[_↦bs_]_ ι ε = act-branches (replace-at ι ε)

-- TODO port the rest
