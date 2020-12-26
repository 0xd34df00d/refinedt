{-# OPTIONS --safe #-}

module Surface.Theorems.Subtyping where

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.WellScoped
open import Surface.WellScoped.CtxSuffix
open import Surface.WellScoped.Membership
open import Surface.Derivations
open import Surface.Theorems.Thinning

<:-narrowing : ∀ Δ
             → Γ ⊢ σ' <: σ
             → Γ , σ  ++ Δ ⊢ τ₂ <: τ₂'
             → Γ , σ' ++ Δ ⊢ τ₂ <: τ₂'
<:-narrowing _ σ-<: (ST-Base oracle is-just) = ST-Base oracle (Oracle.narrowing oracle {- TODO σ-<: -} is-just)
<:-narrowing Δ σ-<: (ST-Arr <:₁ <:₂) = ST-Arr (<:-narrowing Δ σ-<: <:₁) (<:-narrowing (Δ , _) σ-<: <:₂)

<:-trans : Γ ⊢ τ₁ <: τ₂
         → Γ ⊢ τ₂ <: τ₃
         → Γ ⊢ τ₁ <: τ₃
<:-trans (ST-Base oracle ⦃ UoO ⦄ is-just₁) (ST-Base oracle' is-just₂)
  rewrite UniquenessOfOracles.oracles-equal UoO oracle' oracle
        = ST-Base oracle ⦃ UoO ⦄ (Oracle.trans oracle is-just₁ is-just₂)
<:-trans (ST-Arr <:₁ <:₂) (ST-Arr <:₁' <:₂') = ST-Arr (<:-trans <:₁' <:₁) (<:-trans (<:-narrowing ⊘ <:₁' <:₂) <:₂')

mutual
  Γok-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                → Γ ⊢ σ' <: σ
                → Γ ⊢ σ'
                → (Γ , σ  ++ Δ) ok
                → (Γ , σ' ++ Δ) ok
  Γok-narrowing ⊘ <: Γ⊢σ' (TCTX-Bind Γok _) = TCTX-Bind Γok Γ⊢σ'
  Γok-narrowing (Δ , τ) <: Γ⊢σ' (TCTX-Bind Γ,σ,Δok τδ) = TCTX-Bind (Γok-narrowing Δ <: Γ⊢σ' Γ,σ,Δok) (Γ⊢τ-narrowing Δ <: Γ⊢σ' τδ)

  Γ⊢τ-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                → Γ ⊢ σ' <: σ
                → Γ ⊢ σ'
                → Γ , σ  ++ Δ ⊢ τ
                → Γ , σ' ++ Δ ⊢ τ
  Γ⊢τ-narrowing Δ <: Γ⊢σ' (TWF-TrueRef x) = {! !}
  Γ⊢τ-narrowing Δ <: Γ⊢σ' (TWF-Base ε₁δ ε₂δ) = {! !}
  Γ⊢τ-narrowing Δ <: Γ⊢σ' (TWF-Conj τδ τδ₁) = {! !}
  Γ⊢τ-narrowing Δ <: Γ⊢σ' (TWF-Arr τδ τδ₁) = {! !}
  Γ⊢τ-narrowing Δ <: Γ⊢σ' (TWF-ADT consδs) = {! !}

  Γ⊢ε⦂τ-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                  → Γ ⊢ σ' <: σ
                  → Γ ⊢ σ'
                  → Γ , σ  ++ Δ ⊢ ε ⦂ τ
                  → Γ , σ' ++ Δ ⊢ ε ⦂ τ
  Γ⊢ε⦂τ-narrowing Δ <: Γ⊢σ' (T-Unit Γok) = T-Unit (Γok-narrowing Δ <: Γ⊢σ' Γok)
  Γ⊢ε⦂τ-narrowing Δ <: Γ⊢σ' (T-Var Γok x) = {! !}
  Γ⊢ε⦂τ-narrowing Δ <: Γ⊢σ' (T-Abs arrδ εδ) = {! !}
  Γ⊢ε⦂τ-narrowing Δ <: Γ⊢σ' (T-App εδ εδ₁) = T-App (Γ⊢ε⦂τ-narrowing Δ <: Γ⊢σ' εδ) (Γ⊢ε⦂τ-narrowing Δ <: Γ⊢σ' εδ₁)
  Γ⊢ε⦂τ-narrowing Δ <: Γ⊢σ' (T-Case resδ εδ branches-well-typed) = {! !}
  Γ⊢ε⦂τ-narrowing Δ <: Γ⊢σ' (T-Con ≡-prf εδ adtτ) = {! !}
  Γ⊢ε⦂τ-narrowing Δ <: Γ⊢σ' (T-Sub εδ τ'δ <:₁) = {! !}
