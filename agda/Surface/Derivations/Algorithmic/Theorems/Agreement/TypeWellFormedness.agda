{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Agreement.TypeWellFormedness where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (refl)

open import Surface.Syntax
open import Surface.Syntax.Membership
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Helpers
open import Surface.Derivations.Algorithmic.Theorems.Thinning

τ∈Γ-⇒-Γ⊢τ : Γ ok[ θ , φ ]
          → τ ∈ Γ at ι
          → Γ ⊢[ θ , φ ] τ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind Γok τδ) (∈-zero refl) = Γ⊢τ-weakening Γok τδ τδ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind Γok τδ) (∈-suc refl ∈) = Γ⊢τ-weakening Γok τδ (τ∈Γ-⇒-Γ⊢τ Γok ∈)

Γ⊢τ'<:τ-⇒-Γ⊢τ' : Γ ⊢[ θ , E ] τ' <: τ
               → Γ ⊢[ θ , E ] τ'
Γ⊢τ'<:τ-⇒-Γ⊢τ' (ST-Base _ (enriched ρ₁δ) _) = ρ₁δ
Γ⊢τ'<:τ-⇒-Γ⊢τ' (ST-Arr _ _ (enriched τ₁⇒τ₂'δ) _) = τ₁⇒τ₂'δ
Γ⊢τ'<:τ-⇒-Γ⊢τ' (ST-ADT (enriched τδ)) = τδ

Γ⊢τ'<:τ-⇒-Γ⊢τ : Γ ⊢[ θ , E ] τ' <: τ
              → Γ ⊢[ θ , E ] τ
Γ⊢τ'<:τ-⇒-Γ⊢τ (ST-Base _ _ (enriched ρ₂δ)) = ρ₂δ
Γ⊢τ'<:τ-⇒-Γ⊢τ (ST-Arr _ _ _ (enriched τ₁'⇒τ₂δ)) = τ₁'⇒τ₂δ
Γ⊢τ'<:τ-⇒-Γ⊢τ (ST-ADT (enriched τδ)) = τδ

-- Referred to as T-implies-TWF in the paper
Γ⊢ε⦂τ-⇒-Γ⊢τ : Γ ⊢[ θ , φ of κ ] ε ⦂ τ
            → Γ ⊢[ θ , φ ] τ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Unit Γok) = TWF-TrueRef Γok
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Var Γok ∈-prf) = τ∈Γ-⇒-Γ⊢τ Γok ∈-prf
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Abs arrδ _) = arrδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-App _ _ _ resτδ) = resτδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Case resδ _ _) = resδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Con _ _ adtτ) = adtτ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Sub _ superδ _) = superδ
