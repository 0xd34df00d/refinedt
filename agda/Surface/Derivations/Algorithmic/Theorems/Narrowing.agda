{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Narrowing where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Membership
open import Surface.Syntax.Substitution
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Helpers
open import Surface.Derivations.Algorithmic.Theorems.Subtyping
open import Surface.Derivations.Algorithmic.Theorems.Thinning

module _ {σ : SType ℓ} (σ-<:δ : Γ ⊢[ θ ] σ' <: σ) (Γ⊢σ' : Γ ⊢[ θ , φ ] σ') where mutual
  Γok-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                → (Γ , σ  ++ Δ) ok[ θ , φ ]
                → (Γ , σ' ++ Δ) ok[ θ , φ ]
  Γok-narrowing ⊘ (TCTX-Bind Γok τδ) = TCTX-Bind Γok Γ⊢σ'
  Γok-narrowing (Δ , _) (TCTX-Bind Γ,σ,Δ-ok τδ) = TCTX-Bind (Γok-narrowing Δ Γ,σ,Δ-ok) (Γ⊢τ-narrowing Δ τδ)

  Γ⊢τ-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                → Γ , σ  ++ Δ ⊢[ θ , φ ] τ
                → Γ , σ' ++ Δ ⊢[ θ , φ ] τ
  Γ⊢τ-narrowing Δ (TWF-TrueRef Γok) = TWF-TrueRef (Γok-narrowing Δ Γok)
  Γ⊢τ-narrowing Δ (TWF-Base ε₁δ ε₂δ)
    = TWF-Base (Γ⊢ε⦂τ-narrowing (Δ , _) ε₁δ) (Γ⊢ε⦂τ-narrowing (Δ , _) ε₂δ)
  Γ⊢τ-narrowing Δ (TWF-Conj τ₁δ τ₂δ) = TWF-Conj (Γ⊢τ-narrowing Δ τ₁δ) (Γ⊢τ-narrowing Δ τ₂δ)
  Γ⊢τ-narrowing Δ (TWF-Arr τ₁δ τ₂δ) = TWF-Arr (Γ⊢τ-narrowing Δ τ₁δ) (Γ⊢τ-narrowing (Δ , _) τ₂δ)
  Γ⊢τ-narrowing Δ (TWF-ADT consδs) = TWF-ADT (cons-narrowing Δ consδs)

  cons-narrowing : {cons : ADTCons nₐ (k + suc ℓ)}
                 → (Δ : CtxSuffix (suc ℓ) k)
                 → All ((Γ , σ  ++ Δ) ⊢[ θ , φ ]_) cons
                 → All ((Γ , σ' ++ Δ) ⊢[ θ , φ ]_) cons
  cons-narrowing Δ [] = []
  cons-narrowing Δ (τδ ∷ δs) = Γ⊢τ-narrowing Δ τδ ∷ cons-narrowing Δ δs

  branches-narrowing : {cons : ADTCons nₐ (k + suc ℓ)}
                     → {bs : CaseBranches nₐ (k + suc ℓ)}
                     → (Δ : CtxSuffix (suc ℓ) k)
                     → BranchesHaveType θ φ (Γ , σ ++ Δ) cons bs τ
                     → BranchesHaveType θ φ (Γ , σ' ++ Δ) cons bs τ
  branches-narrowing Δ NoBranches = NoBranches
  branches-narrowing Δ (OneMoreBranch εδ bsδ) = OneMoreBranch (Γ⊢ε⦂τ-narrowing (Δ , _) εδ) (branches-narrowing Δ bsδ)

  SVar-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                 → (Γ , σ ++ Δ) ok[ θ , φ ]
                 → τ ∈ Γ , σ ++ Δ at ι
                 → Γ , σ' ++ Δ ⊢[ θ , φ of t-sub ] SVar ι ⦂ τ
  SVar-narrowing ⊘ (TCTX-Bind Γok _) (∈-zero refl)
    = T-Sub (T-Var (TCTX-Bind Γok Γ⊢σ') (∈-zero refl)) (<:-weakening σ-<:δ)
  SVar-narrowing ⊘ (TCTX-Bind Γok τδ) (∈-suc refl ∈) = as-sub (T-Var (TCTX-Bind Γok Γ⊢σ') (∈-suc refl ∈))
  SVar-narrowing (Δ , τ) Γ,σ,Δ-ok (∈-zero refl) = as-sub (T-Var (Γok-narrowing (Δ , _) Γ,σ,Δ-ok) (∈-zero refl))
  SVar-narrowing (Δ , τ) (TCTX-Bind Γ,σ,Δ-ok Γ,σ,Δ⊢τ) (∈-suc refl ∈)
    with εδ ← SVar-narrowing Δ Γ,σ,Δ-ok ∈
       = Γ⊢ε⦂τ-weakening (Γok-narrowing Δ Γ,σ,Δ-ok) (Γ⊢τ-narrowing Δ Γ,σ,Δ⊢τ) εδ

  Γ⊢ε⦂τ-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                  → Γ , σ  ++ Δ ⊢[ θ , φ of κ ] ε ⦂ τ
                  → Γ , σ' ++ Δ ⊢[ θ , φ of t-sub ] ε ⦂ τ
  Γ⊢ε⦂τ-narrowing Δ (T-Unit Γok) = as-sub (T-Unit (Γok-narrowing Δ Γok))
  Γ⊢ε⦂τ-narrowing Δ (T-Var Γok ∈) = SVar-narrowing Δ Γok ∈
  Γ⊢ε⦂τ-narrowing Δ (T-Abs εδ)
    with T-Sub εδ' <:δ ← Γ⊢ε⦂τ-narrowing (Δ , _) εδ
       = T-Sub
           (T-Abs εδ')
           (Γ⊢τ'<:τ-⇒-Γ⊢τ₀⇒τ'<:τ₀⇒τ <:δ)
  Γ⊢ε⦂τ-narrowing Δ (T-App ε₁δ ε₂δ refl)
    with T-Sub ε₁δ' (ST-Arr <:₁δ <:₂δ) ← Γ⊢ε⦂τ-narrowing Δ ε₁δ
       = let ε₂δ'¹ = Γ⊢ε⦂τ-narrowing Δ ε₂δ
             ε₂δ'³ = trans-sub <:₁δ (Γ⊢ε⦂τ-narrowing Δ ε₂δ)
          in T-Sub
              (T-App ε₁δ' ε₂δ'³ refl)
              (sub-Γ⊢τ'<:τ-front ε₂δ'¹ <:₂δ)
  Γ⊢ε⦂τ-narrowing Δ (T-Case resδ εδ branchesδ)
    = as-sub (T-Case (Γ⊢τ-narrowing Δ resδ) (Γ⊢ε⦂τ-narrowing Δ εδ) (branches-narrowing Δ branchesδ))
  Γ⊢ε⦂τ-narrowing Δ (T-Con <:δ εδ adtτ)
    with T-Sub εδ' <:'δ ← Γ⊢ε⦂τ-narrowing Δ εδ
       = as-sub (T-Con (<:-transitive <:'δ (<:-narrowing σ-<:δ Δ <:δ)) εδ' (Γ⊢τ-narrowing Δ adtτ))
  Γ⊢ε⦂τ-narrowing Δ (T-Sub εδ <:δ)
    with T-Sub εδ' <:'δ ← Γ⊢ε⦂τ-narrowing Δ εδ
       = T-Sub εδ' (<:-transitive <:'δ (<:-narrowing σ-<:δ Δ <:δ))
