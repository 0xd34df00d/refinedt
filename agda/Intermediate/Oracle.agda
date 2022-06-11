{-# OPTIONS --safe #-}

module Intermediate.Oracle where

open import Data.Fin using (zero; suc)
open import Data.Maybe
open import Data.Nat.Base using (_+_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Common.Helpers

open import Intermediate.Syntax
open import Intermediate.Syntax.Subcontext
import Intermediate.Syntax.Renaming as R

open import Core.Syntax using (CExpr)
open import Core.Syntax.Renaming as CR using (act-ε)

record PositiveDecision (ℓ : ℕ) : Set where
  constructor MkPD
  field
    <:-ε : CExpr ℓ

record Oracle : Set where
  constructor MkOracle
  open R
  field
    decide : (Γ : Ctx ℓ)
           → (b : BaseType)
           → (ρ₁ ρ₂ : IRefinement (suc ℓ))
           → Maybe (PositiveDecision ℓ)
    thin   : ∀ {Γ : Ctx (k + ℓ)} {Γ' : Ctx (suc k + ℓ)} {ρ₁ ρ₂ : IRefinement (suc k + ℓ)}
           → (Γ⊂Γ' : k by Γ ⊂' Γ')
           → Is-just (decide Γ b ρ₁ ρ₂)
           → Is-just (decide Γ' b (R.act-ρ (ext-k' (suc k) suc) ρ₁) (act-ρ (ext-k' (suc k) suc) ρ₂))
    trans : Is-just (decide Γ b ρ₁ ρ₂)
          → Is-just (decide Γ b ρ₂ ρ₃)
          → Is-just (decide Γ b ρ₁ ρ₃)

    thin-ε : ∀ {Γ : Ctx (k + ℓ)} {Γ' : Ctx (suc k + ℓ)} {ρ₁ ρ₂ : IRefinement (suc k + ℓ)}
           → (is-just : Is-just (decide Γ b ρ₁ ρ₂))
           → (Γ⊂Γ' : k by Γ ⊂' Γ')
           → PositiveDecision.<:-ε (to-witness (thin Γ⊂Γ' is-just))
             ≡
             CR.act-ε (ext-k' k suc) (PositiveDecision.<:-ε (to-witness is-just))
-- TODO when all is done, check if any of the above properties are not needed anymore
-- See also .θ-Props modules elsewhere for any additional properties
-- not expressed here due to strict positivity or similar reasons.
