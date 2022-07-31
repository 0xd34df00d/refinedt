{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Agreement.TypeWellFormedness where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (refl)

open import Surface.Syntax
open import Surface.Syntax.Membership
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Agreement.Lemmas
open import Surface.Derivations.Algorithmic.Theorems.Helpers
open import Surface.Derivations.Algorithmic.Theorems.Substitution
open import Surface.Derivations.Algorithmic.Theorems.Thinning

τ∈Γ-⇒-Γ⊢τ : Γ ok[ θ , M ]
          → τ ∈ Γ at ι
          → Γ ⊢[ θ , M ] τ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind Γok τδ) (∈-zero refl) = Γ⊢τ-weakening Γok τδ τδ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind Γok τδ) (∈-suc refl ∈) = Γ⊢τ-weakening Γok τδ (τ∈Γ-⇒-Γ⊢τ Γok ∈)

-- Referred to as T-implies-TWF in the paper
Γ⊢ε⦂τ-⇒-Γ⊢τ : Γ ⊢[ θ , M of not-t-sub ] ε ⦂ τ
            → Γ ⊢[ θ , M ] τ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Unit Γok) = TWF-TrueRef Γok
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Var Γok ∈-prf) = τ∈Γ-⇒-Γ⊢τ Γok ∈-prf
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Abs εδ) = Γ,τ₁⊢τ₂-⇒-Γ⊢τ₁⇒τ₂ (Γ⊢ε⦂τ-⇒-Γ⊢τ εδ)
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-App ε₁δ ε₂δ refl) with TWF-Arr _ τ₂δ ← Γ⊢ε⦂τ-⇒-Γ⊢τ ε₁δ = sub-Γ⊢τ-front ε₂δ τ₂δ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Case resδ _ _) = resδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Con _ _ adtτ) = adtτ
