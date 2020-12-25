{-# OPTIONS --safe #-}

module Surface.Theorems.Subtyping where

open import Surface.WellScoped
open import Surface.Derivations

Γ⊢τ'<:τ-⇒-Γ⊢τ : Γ ⊢ τ' <: τ
              → Γ ⊢ τ
Γ⊢τ'<:τ-⇒-Γ⊢τ (ST-Base oracle x) = {! !}
Γ⊢τ'<:τ-⇒-Γ⊢τ (ST-Arr <: <:₁) = {! !}

Γ⊢τ'<:τ-⇒-Γ⊢τ' : Γ ⊢ τ' <: τ
               → Γ ⊢ τ'
Γ⊢τ'<:τ-⇒-Γ⊢τ' (ST-Base oracle x) = {! !}
Γ⊢τ'<:τ-⇒-Γ⊢τ' (ST-Arr <:₁ <:₂) = TWF-Arr (Γ⊢τ'<:τ-⇒-Γ⊢τ <:₁) {! !}


<:-in-Γok : Γ ⊢ τ' <: τ
          → (Γ , τ) ok
          → (Γ , τ') ok
<:-in-Γok <: (TCTX-Bind Γok τδ) = TCTX-Bind Γok {! !}

<:-in-Γ⊢ε⦂τ : Γ ⊢ τ' <: τ
            → Γ , τ ⊢ ε ⦂ τ₀
            → Γ , τ' ⊢ ε ⦂ τ₀
<:-in-Γ⊢ε⦂τ <: (T-Unit Γok) = T-Unit {! !}
<:-in-Γ⊢ε⦂τ <: (T-Var Γok x) = {! !}
<:-in-Γ⊢ε⦂τ <: (T-Abs arrδ εδ) = {! !}
<:-in-Γ⊢ε⦂τ <: (T-App εδ εδ₁) = {! !}
<:-in-Γ⊢ε⦂τ <: (T-Case resδ εδ branches-well-typed) = {! !}
<:-in-Γ⊢ε⦂τ <: (T-Con ≡-prf εδ adtτ) = {! !}
<:-in-Γ⊢ε⦂τ <: (T-Sub εδ x x₁) = {! !}
