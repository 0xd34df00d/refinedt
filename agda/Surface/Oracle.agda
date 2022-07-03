{-# OPTIONS --safe #-}

module Surface.Oracle where

open import Data.Fin using (zero; suc)
open import Data.Maybe using (Maybe; Is-just; to-witness)
open import Data.Nat.Base using (_+_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Common.Helpers

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Subcontext
import Surface.Syntax.Renaming as R
import Surface.Syntax.Substitution as S

open import Core.Syntax using (CExpr)
open import Core.Syntax.Renaming as CR using (act-ε)

record PositiveDecision (ℓ : ℕ) : Set where
  constructor MkPD
  field
    <:-ε : CExpr ℓ

record Oracle : Set where
  inductive
  constructor MkOracle
  open R
  field
    decide : (Γ : Ctx ℓ)
           → (b : BaseType)
           → (ρ₁ ρ₂ : Refinement (suc ℓ))
           → Maybe (PositiveDecision ℓ)
    <:-refl : (Γ : Ctx ℓ)
            → (b : BaseType)
            → (ρ : Refinement (suc ℓ))
            → Is-just (decide Γ b ρ ρ)
    thin : ∀ {Γ : Ctx (k + ℓ)} {Γ' : Ctx (suc k + ℓ)} {ρ₁ ρ₂ : Refinement (suc k + ℓ)}
         → (Γ⊂Γ' : k by Γ ⊂' Γ')
         → Is-just (decide Γ b ρ₁ ρ₂)
         → Is-just (decide Γ' b (R.act-ρ (ext-k' (suc k) suc) ρ₁) (act-ρ (ext-k' (suc k) suc) ρ₂))
    subst : ∀ {Δ : ,-CtxSuffix ℓ σ k} {ρ₁ ρ₂ : Refinement (suc (suc k + ℓ))}
          -- TODO add this back when parametrizing everything by an oracle: → Γ ⊢ ε ⦂ σ
          → Is-just (decide (Γ ,σ, Δ) b ρ₁ ρ₂)
          → Is-just (decide (Γ ++ ([↦Δ ε ] Δ)) b
                        (S.act-ρ (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) ρ₁)
                        (S.act-ρ (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) ρ₂))
    trans : Is-just (decide Γ b ρ₁ ρ₂)
          → Is-just (decide Γ b ρ₂ ρ₃)
          → Is-just (decide Γ b ρ₁ ρ₃)
    narrowing : Is-just (decide (Γ , σ  ++ Δ) b ρ₁ ρ₂)
              -- TODO add this back when parametrizing everything by an oracle: → Γ ⊢ σ' <: σ
              → Is-just (decide (Γ , σ' ++ Δ) b ρ₁ ρ₂)

    thin-ε : ∀ {Γ : Ctx (k + ℓ)} {Γ' : Ctx (suc k + ℓ)} {ρ₁ ρ₂ : Refinement (suc k + ℓ)}
           → (is-just : Is-just (decide Γ b ρ₁ ρ₂))
           → (Γ⊂Γ' : k by Γ ⊂' Γ')
           → PositiveDecision.<:-ε (to-witness (thin Γ⊂Γ' is-just))
             ≡
             CR.act-ε (ext-k' k suc) (PositiveDecision.<:-ε (to-witness is-just))
