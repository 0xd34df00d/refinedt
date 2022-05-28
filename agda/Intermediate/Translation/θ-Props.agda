{-# OPTIONS --safe #-}

{-
This module lists requirements on an Oracle
needed to prove that the translation is well-behaved.

Since the properties here depend both on typing derivations in Intermediate.Derivations.*
as well as on the translation function definitions in Translation.Typed,
they cannot be (easily) defined in Intermediate.Oracle without introducing circular deps.
Hence, they are defined separately here.
-}

open import Intermediate.Oracle

module Intermediate.Translation.θ-Props(θ : Oracle) where

open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Intermediate.Derivations.Algorithmic hiding (θ)
open import Intermediate.Syntax as I renaming (Γ to Γⁱ; τ to τⁱ; σ to σⁱ; ε to εⁱ)
open import Intermediate.Syntax.CtxSuffix as I
open import Intermediate.Syntax.Substitution as IS

open import Core.Syntax
open import Core.Syntax.Substitution

open import Intermediate.Translation.Typed

record Props : Set where
  constructor MkProps
  open PositiveDecision
  field
    sub-<: : ∀ {Γⁱ : I.Ctx ℓ}
           → (Δⁱ : ,-CtxSuffix ℓ σⁱ k)
           → (εδ : [ θ ] Γⁱ ⊢ εⁱ ⦂ τⁱ)
           → (is-just₁ : Is-just (Oracle.decide θ (Γⁱ ,σ, Δⁱ)
                                                b ρ₁ ρ₂))
           → (is-just₂ : Is-just (Oracle.decide θ (Γⁱ ++ [↦Δ εⁱ ] Δⁱ)
                                                b ([ ℓ ↦ρ< εⁱ ] ρ₁) ([ ℓ ↦ρ< εⁱ ] ρ₂)))
           → <:-ε (to-witness is-just₂)
             ≡
             ([ ℓ ↦' μ-ε εδ ] (<:-ε (to-witness is-just₁)))
