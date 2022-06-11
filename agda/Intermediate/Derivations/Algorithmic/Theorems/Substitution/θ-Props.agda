{-# OPTIONS --safe #-}

open import Intermediate.Oracle

module Intermediate.Derivations.Algorithmic.Theorems.Substitution.θ-Props(θ : Oracle) where

open import Data.Maybe using (Is-just)

open import Common.Helpers

open import Intermediate.Syntax
open import Intermediate.Syntax.CtxSuffix
import Intermediate.Syntax.Renaming as R
import Intermediate.Syntax.Substitution as S
open import Intermediate.Derivations.Algorithmic hiding (θ)

record Props : Set where
  constructor MkProps
  field
    subst  : ∀ {Δ : ,-CtxSuffix ℓ σ k} {ρ₁ ρ₂ : IRefinement (suc (suc k + ℓ))}
           → [ θ ] Γ ⊢ ε ⦂ σ
           → Is-just (Oracle.decide θ (Γ ,σ, Δ) b ρ₁ ρ₂)
           → Is-just (Oracle.decide θ (Γ ++ ([↦Δ ε ] Δ)) b
                        (S.act-ρ (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) ρ₁)
                        (S.act-ρ (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) ρ₂))
