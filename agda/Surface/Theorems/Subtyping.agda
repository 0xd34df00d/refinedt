{-# OPTIONS --safe #-}

module Surface.Theorems.Subtyping where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.WellScoped
open import Surface.WellScoped.Membership
open import Surface.Derivations
open import Surface.Theorems.Thinning

<:-trans : Γ ⊢ τ₁ <: τ₂
         → Γ ⊢ τ₂ <: τ₃
         → Γ ⊢ τ₁ <: τ₃
<:-trans (ST-Base oracle ⦃ UoO ⦄ is-just₁) (ST-Base oracle' is-just₂)
  rewrite UniquenessOfOracles.oracles-equal UoO oracle' oracle
        = ST-Base oracle ⦃ UoO ⦄ (Oracle.trans oracle is-just₁ is-just₂)
<:-trans (ST-Arr <:₁ <:₂) (ST-Arr <:₁' <:₂') = ST-Arr (<:-trans <:₁' <:₁) {! !} -- ST-Arr {! !} {! !}
-- Goal : Γ ⊢ τ₁ ⇒ τ₂ <: (τ₁' ⇒ τ₂')

<:-in-Γ⊢ε⦂τ : Γ ⊢ τ' <: τ
            → Γ ⊢ τ'
            → Γ , τ ⊢ ε ⦂ τ₀
            → Γ , τ' ⊢ ε ⦂ τ₀
<:-in-Γ⊢ε⦂τ <: Γ⊢τ' (T-Unit (TCTX-Bind Γok τδ)) = T-Unit (TCTX-Bind Γok Γ⊢τ')
<:-in-Γ⊢ε⦂τ <: Γ⊢τ' (T-Var (TCTX-Bind Γok τδ) (∈-zero refl)) = T-Sub (T-Var (TCTX-Bind Γok Γ⊢τ') (∈-zero refl)) (twf-weakening Γok Γ⊢τ' τδ) (st-weakening Γok <:)
<:-in-Γ⊢ε⦂τ <: Γ⊢τ' (T-Var (TCTX-Bind Γok τδ) (∈-suc refl x)) = T-Var (TCTX-Bind Γok Γ⊢τ') (∈-suc refl x)
<:-in-Γ⊢ε⦂τ <: Γ⊢τ' (T-Abs arrδ εδ) = {! !}
<:-in-Γ⊢ε⦂τ <: Γ⊢τ' (T-App εδ εδ₁) = T-App (<:-in-Γ⊢ε⦂τ <: Γ⊢τ' εδ) (<:-in-Γ⊢ε⦂τ <: Γ⊢τ' εδ₁)
<:-in-Γ⊢ε⦂τ <: Γ⊢τ' (T-Case resδ εδ branches-well-typed) = {! !}
<:-in-Γ⊢ε⦂τ <: Γ⊢τ' (T-Con ≡-prf εδ adtτ) = {! !}
<:-in-Γ⊢ε⦂τ <: Γ⊢τ' (T-Sub εδ x x₁) = {! !}
