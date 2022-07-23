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
open import Surface.Derivations.Algorithmic.Theorems.Agreement.Lemmas

τ∈Γ-⇒-Γ⊢τ : Γ ok[ θ , φ ]
          → τ ∈ Γ at ι
          → Γ ⊢[ θ , φ ] τ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind Γok τδ) (∈-zero refl) = Γ⊢τ-weakening Γok τδ τδ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind Γok τδ) (∈-suc refl ∈) = Γ⊢τ-weakening Γok τδ (τ∈Γ-⇒-Γ⊢τ Γok ∈)

-- Referred to as T-implies-TWF in the paper
Γ⊢ε⦂τ-⇒-Γ⊢τ : Γ ⊢[ θ , φ of not-t-sub ] ε ⦂ τ
            → Γ ⊢[ θ , φ ] τ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Unit Γok) = TWF-TrueRef Γok
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Var Γok ∈-prf) = τ∈Γ-⇒-Γ⊢τ Γok ∈-prf
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Abs εδ) = Γ,τ₁⊢τ₂-⇒-Γ⊢τ₁⇒τ₂ (Γ⊢ε⦂τ-⇒-Γ⊢τ εδ)
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-App _ _ _ resτδ) = resτδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Case resδ _ _) = resδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Con _ _ adtτ) = adtτ
