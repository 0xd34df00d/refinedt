module Surface.Derivations.Algorithmic.Theorems.Narrowing where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Membership
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Subtyping
open import Surface.Derivations.Algorithmic.Theorems.Thinning

module M {σ : SType ℓ} (σ-<:δ : Γ ⊢[ θ , φ ] σ' <: σ) (Γ⊢σ' : Γ ⊢[ θ , φ ] σ') where mutual
  <:-narrowing : ∀ Δ
               → Γ , σ  ++ Δ ⊢[ θ , φ ] τ₂ <: τ₂'
               → Γ , σ' ++ Δ ⊢[ θ , φ ] τ₂ <: τ₂'
  <:-narrowing Δ <:δ = {! !}

  Γok-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                → (Γ , σ  ++ Δ) ok[ θ , φ ]
                → (Γ , σ' ++ Δ) ok[ θ , φ ]
  Γok-narrowing Δ Γδ = {! Γδ !}

  Γ⊢τ-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                → Γ , σ  ++ Δ ⊢[ θ , φ ] τ
                → Γ , σ' ++ Δ ⊢[ θ , φ ] τ
  Γ⊢τ-narrowing Δ (TWF-TrueRef Γok) = TWF-TrueRef (Γok-narrowing Δ Γok)
  Γ⊢τ-narrowing Δ (TWF-Base ε₁δ ε₂δ)
    = let ε₁δ' = as-sub (Γ⊢ε⦂τ-narrowing (Δ , _) ε₁δ)
          ε₂δ' = as-sub (Γ⊢ε⦂τ-narrowing (Δ , _) ε₂δ)
       in TWF-Base ε₁δ' ε₂δ'
  Γ⊢τ-narrowing Δ (TWF-Conj τδ τδ₁) = {! !}
  Γ⊢τ-narrowing Δ (TWF-Arr τδ τδ₁) = {! !}
  Γ⊢τ-narrowing Δ (TWF-ADT consδs) = {! !}

  Γ⊢ε⦂τ-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                  → Γ , σ  ++ Δ ⊢[ θ , φ of κ ] ε ⦂ τ
                  → ∃[ κ' ] (Γ , σ' ++ Δ ⊢[ θ , φ of κ' ] ε ⦂ τ)
  Γ⊢ε⦂τ-narrowing Δ (T-Unit Γok) = ⟨ _ , T-Unit (Γok-narrowing Δ Γok) ⟩
  Γ⊢ε⦂τ-narrowing Δ (T-Var Γok x) = {! !}
  Γ⊢ε⦂τ-narrowing Δ (T-Abs arrδ εδ) = {! !}
  Γ⊢ε⦂τ-narrowing Δ (T-App εδ εδ₁ resτ-≡ resτδ) = {! !}
  Γ⊢ε⦂τ-narrowing Δ (T-Case resδ εδ branches-well-typed) = {! !}
  Γ⊢ε⦂τ-narrowing Δ (T-Con ≡-prf εδ adtτ) = {! !}
  Γ⊢ε⦂τ-narrowing Δ (T-Sub εδ τδ <:δ) = {! !}

open M public
