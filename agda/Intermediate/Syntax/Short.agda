{-# OPTIONS --safe #-}

module Intermediate.Syntax.Short where

import Data.Fin as F using (#_)
import Data.Nat.Properties as ℕₚ
open import Relation.Nullary.Decidable.Core

open import Intermediate.Syntax public

infixl 25 _∙_
_∙_ : ITerm ℓ → ITerm ℓ → ITerm ℓ
_∙_ = IApp

infixr 20 ƛ_⇉_
ƛ_⇉_ : IType ℓ → ITerm (suc ℓ) → ITerm ℓ
ƛ_⇉_ = ILam


infix 30 #_

#_ : ∀ m {ℓ} {m<ℓ : True (suc m ℕₚ.≤? ℓ)} → ITerm ℓ
#_ m {ℓ} {m<ℓ} = IVar (F.#_ m {ℓ} {m<ℓ})

#0 : ITerm (suc ℓ)
#0 = # 0

#1 : ITerm (suc (suc ℓ))
#1 = # 1

#2 : ITerm (suc (suc (suc ℓ)))
#2 = # 2
