{-# OPTIONS --safe #-}

module Core.Syntax.Substitution.Stable where

open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Syntax
open import Core.Syntax.Renaming as R
open import Core.Syntax.Substitution as S
open import Core.Syntax.Substitution.Distributivity

replace-weakened-ε-zero : (ε' ε : CExpr ℓ)
                        → [ zero ↦ ε' ] (weaken-ε ε) ≡ ε
replace-weakened-ε-zero ε' ε
  rewrite σ-ρ-distr-ε (replace-at zero ε') suc ε
        | S.act-ε-id (λ _ → refl) ε
        = refl
