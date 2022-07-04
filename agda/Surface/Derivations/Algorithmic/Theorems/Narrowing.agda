module Surface.Derivations.Algorithmic.Theorems.Narrowing where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Membership
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Subtyping
open import Surface.Derivations.Algorithmic.Theorems.Thinning

mutual
  <:-narrowing : ∀ Δ
               → Γ ⊢[ θ , φ ] σ' <: σ
               → Enrich (Γ ⊢[ θ , φ ] σ') φ
               → Γ , σ  ++ Δ ⊢[ θ , φ ] τ₂ <: τ₂'
               → Γ , σ' ++ Δ ⊢[ θ , φ ] τ₂ <: τ₂'
  <:-narrowing Δ σ-<:δ Γ⊢σ' <:δ = {! !}

  Γok-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                → Γ ⊢[ θ , φ ] σ' <: σ
                → Γ ⊢[ θ , φ ] σ'
                → (Γ , σ  ++ Δ) ok[ θ , φ ]
                → (Γ , σ' ++ Δ) ok[ θ , φ ]
  Γok-narrowing Δ σ-<:δ Γ⊢σ' Γδ = {! Γδ !}

  Γ⊢τ-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                → Γ ⊢[ θ , φ ] σ' <: σ
                → Γ ⊢[ θ , φ ] σ'
                → Γ , σ  ++ Δ ⊢[ θ , φ ] τ
                → Γ , σ' ++ Δ ⊢[ θ , φ ] τ
  Γ⊢τ-narrowing Δ σ-<:δ Γ⊢σ' (TWF-TrueRef Γok) = TWF-TrueRef (Γok-narrowing Δ σ-<:δ Γ⊢σ' Γok)
  Γ⊢τ-narrowing Δ σ-<:δ Γ⊢σ' (TWF-Base ε₁δ ε₂δ)
    = let ε₁δ' = as-sub (Γ⊢ε⦂τ-narrowing (Δ , _) σ-<:δ Γ⊢σ' ε₁δ)
          ε₂δ' = as-sub (Γ⊢ε⦂τ-narrowing (Δ , _) σ-<:δ Γ⊢σ' ε₂δ)
       in TWF-Base ε₁δ' ε₂δ'
  Γ⊢τ-narrowing Δ σ-<:δ Γ⊢σ' (TWF-Conj τδ τδ₁) = {! !}
  Γ⊢τ-narrowing Δ σ-<:δ Γ⊢σ' (TWF-Arr τδ τδ₁) = {! !}
  Γ⊢τ-narrowing Δ σ-<:δ Γ⊢σ' (TWF-ADT consδs) = {! !}

  Γ⊢ε⦂τ-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                  → Γ ⊢[ θ , φ ] σ' <: σ
                  → Γ ⊢[ θ , φ ] σ'
                  → Γ , σ  ++ Δ ⊢[ θ , φ of κ ] ε ⦂ τ
                  → ∃[ κ' ] (Γ , σ' ++ Δ ⊢[ θ , φ of κ' ] ε ⦂ τ)
  Γ⊢ε⦂τ-narrowing Δ σ-<:δ Γ⊢σ' (T-Unit Γok) = ⟨ _ , T-Unit (Γok-narrowing Δ σ-<:δ Γ⊢σ' Γok) ⟩
  Γ⊢ε⦂τ-narrowing Δ σ-<:δ Γ⊢σ' (T-Var Γok x) = {! !}
  Γ⊢ε⦂τ-narrowing Δ σ-<:δ Γ⊢σ' (T-Abs arrδ εδ) = {! !}
  Γ⊢ε⦂τ-narrowing Δ σ-<:δ Γ⊢σ' (T-App εδ εδ₁ resτ-≡ resτδ) = {! !}
  Γ⊢ε⦂τ-narrowing Δ σ-<:δ Γ⊢σ' (T-Case resδ εδ branches-well-typed) = {! !}
  Γ⊢ε⦂τ-narrowing Δ σ-<:δ Γ⊢σ' (T-Con ≡-prf εδ adtτ) = {! !}
  Γ⊢ε⦂τ-narrowing Δ σ-<:δ Γ⊢σ' (T-Sub εδ τδ <:δ) = {! !}
