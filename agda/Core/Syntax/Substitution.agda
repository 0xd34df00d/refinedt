{-# OPTIONS --safe #-}

module Core.Syntax.Substitution where
open import Data.Fin using (suc; zero)

open import Common.Helpers
open import Core.Syntax
import      Core.Syntax.Renaming as R
open import Core.Syntax.Actions (record { Target = CExpr
                                        ; var-action = λ ε → ε
                                        ; ext = λ where _ zero → CVar zero
                                                        σ (suc n) → R.weaken-ε (σ n)
                                        }) public

replace-at : Fin (suc ℓ) → CExpr ℓ → Fin (suc ℓ) → CExpr ℓ
replace-at = replace-at-generic CVar

SubstOn : (ℕ → Set) → Set
SubstOn Ty = ∀ {ℓ} → Fin (suc ℓ) → CExpr ℓ → Ty (suc ℓ) → Ty ℓ

infixr 6 [_↦ε_]_ [_↦c_]_ [_↦bs_]_
[_↦ε_]_ : SubstOn CExpr
[_↦ε_]_ idx ε = act-ε (replace-at idx ε)

[_↦c_]_ : SubstOn (ADTCons nₐ)
[_↦c_]_ idx ε = act-cons (replace-at idx ε)

[_↦bs_]_ : SubstOn (CaseBranches nₐ)
[_↦bs_]_ idx ε = act-branches (replace-at idx ε)
