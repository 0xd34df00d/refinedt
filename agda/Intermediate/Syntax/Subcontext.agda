{-# OPTIONS --safe #-}

module Intermediate.Syntax.Subcontext where

open import Data.Fin.Base using (zero; suc)
open import Data.Nat.Base using (zero; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Helpers
open import Intermediate.Syntax
open import Intermediate.Syntax.Renaming

infix 4 _by_⊂'_
data _by_⊂'_ : (k : ℕ) → Ctx (k + ℓ) → Ctx (suc (k + ℓ)) → Set where
  ignore-head : zero by Γ ⊂' Γ , τ
  append-both : {Γ : Ctx (k + ℓ)}
              → k by Γ ⊂' Γ'
              → suc k by Γ , τ ⊂' Γ' , act-τ (ext-k' k suc) τ

ext-k'-suc-commute : (k : ℕ)
                   → (τ : IType (k + ℓ))
                   → act-τ (ext-k' (suc k) suc) (act-τ suc τ) ≡ act-τ suc (act-τ (ext-k' k suc) τ)
ext-k'-suc-commute k τ
  rewrite act-τ-distr suc (ext (ext-k' k suc)) τ
        | act-τ-distr (ext-k' k suc) suc τ
        = refl
