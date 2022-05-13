{-# OPTIONS --safe #-}

module Intermediate.Derivations.Algorithmic.Theorems.Agreement.TypeWellFormedness where

open import Data.Fin.Base
open import Data.Nat.Base
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (refl)

open import Intermediate.Syntax
open import Intermediate.Syntax.Membership
open import Intermediate.Derivations.Algorithmic
open import Intermediate.Derivations.Algorithmic.Theorems.Helpers
open import Intermediate.Derivations.Algorithmic.Theorems.Thinning

τ∈Γ-⇒-Γ⊢τ : [ θ ] Γ ok
          → τ ∈ Γ at ι
          → [ θ ] Γ ⊢ τ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind Γok τδ) (∈-zero refl) = Γ⊢τ-weakening Γok τδ τδ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind Γok τδ) (∈-suc refl ∈) = Γ⊢τ-weakening Γok τδ (τ∈Γ-⇒-Γ⊢τ Γok ∈)

Γ⊢τ'<:τ-⇒-Γ⊢τ : [ θ ] Γ ⊢ τ' <: τ
              → [ θ ] Γ ⊢ τ
Γ⊢τ'<:τ-⇒-Γ⊢τ (ST-Base _ _ τδ) = τδ
Γ⊢τ'<:τ-⇒-Γ⊢τ (ST-Arr _ _ _ τδ) = τδ

Γ⊢τ'<:τ-⇒-Γ⊢τ' : [ θ ] Γ ⊢ τ' <: τ
               → [ θ ] Γ ⊢ τ'
Γ⊢τ'<:τ-⇒-Γ⊢τ' (ST-Base _ τ'δ _) = τ'δ
Γ⊢τ'<:τ-⇒-Γ⊢τ' (ST-Arr _ _ τ'δ _) = τ'δ

-- Referred to as T-implies-TWF in the paper
Γ⊢ε⦂τ-⇒-Γ⊢τ : [ θ ] Γ ⊢ ε ⦂ τ
            → [ θ ] Γ ⊢ τ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Unit Γok) = TWF-TrueRef Γok
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Var Γok ∈-prf) = τ∈Γ-⇒-Γ⊢τ Γok ∈-prf
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Abs arrδ _) = arrδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-App _ _ _ resτδ) = resτδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Case resδ _ _) = resδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Con _ _ adtτ) = adtτ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-SubW <: _) = Γ⊢τ'<:τ-⇒-Γ⊢τ <:
