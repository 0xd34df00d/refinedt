{-# OPTIONS --safe #-}

module Intermediate.Syntax.Renaming where

open import Data.Fin using (zero; suc; raise)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat using (_+_; zero; suc)
open import Data.Vec
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import Common.Helpers
open import Common.Types
open import Data.Fin.Extra
open import Intermediate.Syntax
open import Intermediate.Syntax.Actions (record { Target = Fin
                                                ; var-action = λ ι → SVar ι
                                                ; ext = ext-ρ
                                                }) public

weaken-τ : SType ℓ → SType (suc ℓ)
weaken-τ = act-τ suc

weaken-ε : STerm ℓ → STerm (suc ℓ)
weaken-ε = act-ε suc

weaken-ρ : Refinement ℓ → Refinement (suc ℓ)
weaken-ρ = act-ρ suc

weaken-τ-k : ∀ k → SType ℓ → SType (k + ℓ)
weaken-τ-k k = act-τ (raise k)

weaken-ε-k : ∀ k → STerm ℓ → STerm (k + ℓ)
weaken-ε-k k = act-ε (raise k)

-- TODO port the rest
