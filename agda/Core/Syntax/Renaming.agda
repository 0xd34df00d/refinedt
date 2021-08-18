{-# OPTIONS --safe #-}

module Core.Syntax.Renaming where

open import Data.Nat using (zero; suc)
open import Data.Fin using (zero; suc)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Common.Helpers
open import Core.Syntax
open import Core.Syntax.Actions (record { Target = Fin
                                        ; var-action = λ ι → CVar ι
                                        ; ext = ext-ρ
                                        }) public

open import Core.Syntax.Injectivity
open import Core.Syntax.Actions.Lemmas var-action-record (record { ≡-ext = λ where x-≡ zero → refl
                                                                                   x-≡ (suc ι) → cong suc (x-≡ ι)
                                                                 ; ext-id = λ where f-id zero → refl
                                                                                    f-id (suc ι) → cong (CVar ∘ suc) (CVar-injective (f-id ι))
                                                                 }) public

weaken-ε : CExpr ℓ → CExpr (suc ℓ)
weaken-ε = act-ε suc

weaken-cons : ADTCons nₐ ℓ → ADTCons nₐ (suc ℓ)
weaken-cons = act-cons suc

weaken-ε-k : ∀ k → CExpr ℓ → CExpr (k + ℓ)
weaken-ε-k zero ε = ε
weaken-ε-k (suc k) ε = weaken-ε (weaken-ε-k k ε)
