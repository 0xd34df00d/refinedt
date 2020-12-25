{-# OPTIONS --safe #-}

open import Surface.Oracle

module Surface.OracleProps(ω : Oracle) where

open import Data.Maybe using (Is-just)
open import Data.Nat.Base using (_+_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Surface.WellScoped
open import Surface.WellScoped.CtxPrefix
open import Surface.WellScoped.Membership
open import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.Substitution as S
open import Surface.Derivations ω

record OracleProps : Set where
  constructor MkOracleProps
  open Oracle ω
  field
    thin   : ∀ {Γ : Ctx ℓ} {Γ' : Ctx ℓ'}
           → (Γ⊂Γ' : Γ ⊂ Γ')
           → Is-just (decide Γ b ρ₁ ρ₂)
           → Is-just (decide Γ' b (R.act-ρ (R.ext (_⊂_.ρ Γ⊂Γ')) ρ₁) (R.act-ρ (R.ext (_⊂_.ρ Γ⊂Γ')) ρ₂))
    ⇒-consistent
           : ∀ {ρ}
           → Is-just (decide ⊘ b Τ ρ)
           → ρ ≡ Τ
    ⇒-complete
           : ∀ {ρ}
           → Is-just (decide Γ b ρ ρ)
    subst  : ∀ {k} {Γ : Ctx ℓ} {Γ,σ,Δ : Ctx (suc k + ℓ)} {ρ₁ ρ₂ : Refinement (suc (suc k + ℓ))}
           → Γ ⊢ ε ⦂ σ
           → Γ prefix-at suc k of Γ,σ,Δ
           → weaken-τ-k (suc k) σ ∈ Γ,σ,Δ at ctx-idx k
           → Is-just (decide Γ,σ,Δ b ρ₁ ρ₂)
           → Is-just (decide ([ ℓ ↦Γ ε ] Γ,σ,Δ) b
                        (S.act-ρ (S.ext (S.replace-at (S.ctx-idx k) (R.weaken-ε-k k ε))) ρ₁)
                        (S.act-ρ (S.ext (S.replace-at (S.ctx-idx k) (R.weaken-ε-k k ε))) ρ₂))
