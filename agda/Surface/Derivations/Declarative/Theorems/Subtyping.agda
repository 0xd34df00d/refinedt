{-# OPTIONS --safe #-}

module Surface.Derivations.Declarative.Theorems.Subtyping where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Membership
open import Surface.Derivations.Declarative
open import Surface.Derivations.Declarative.Theorems.Thinning

-- Referred to as typing-narrowing in the paper
module _ {σ : SType ℓ} (σ-<: : Γ ⊢[ θ ] σ' <: σ) (Γ⊢σ' : Γ ⊢[ θ ] σ') where mutual
  <:-narrowing : (Δ : CtxSuffix (suc ℓ) k)
               → Γ , σ  ++ Δ ⊢[ θ ] τ₂ <: τ₂'
               → Γ , σ' ++ Δ ⊢[ θ ] τ₂ <: τ₂'
  <:-narrowing _ (ST-Base is-just) = ST-Base (Oracle.narrowing θ {- TODO σ-<: -} is-just)
  <:-narrowing Δ (ST-Arr <:₁ <:₂)
    = ST-Arr
        (<:-narrowing Δ <:₁)
        (<:-narrowing (Δ , _) <:₂)

  Γok-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                → (Γ , σ  ++ Δ) ok[ θ ]
                → (Γ , σ' ++ Δ) ok[ θ ]
  Γok-narrowing ⊘ (TCTX-Bind Γok _) = TCTX-Bind Γok Γ⊢σ'
  Γok-narrowing (Δ , τ) (TCTX-Bind Γ,σ,Δok τδ) = TCTX-Bind (Γok-narrowing Δ Γ,σ,Δok) (Γ⊢τ-narrowing Δ τδ)

  Γ⊢τ-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                → Γ , σ  ++ Δ ⊢[ θ ] τ
                → Γ , σ' ++ Δ ⊢[ θ ] τ
  Γ⊢τ-narrowing Δ (TWF-TrueRef Γok) = TWF-TrueRef (Γok-narrowing Δ Γok)
  Γ⊢τ-narrowing Δ (TWF-Base ε₁δ ε₂δ) = TWF-Base (Γ⊢ε⦂τ-narrowing (Δ , _) ε₁δ) (Γ⊢ε⦂τ-narrowing (Δ , _) ε₂δ)
  Γ⊢τ-narrowing Δ (TWF-Conj ρ₁δ ρ₂δ) = TWF-Conj (Γ⊢τ-narrowing Δ ρ₁δ) (Γ⊢τ-narrowing Δ ρ₂δ)
  Γ⊢τ-narrowing Δ (TWF-Arr argδ resδ) = TWF-Arr (Γ⊢τ-narrowing Δ argδ) (Γ⊢τ-narrowing (Δ , _) resδ)
  Γ⊢τ-narrowing Δ (TWF-ADT consδs) = TWF-ADT (narrow-cons Δ consδs)
    where
    narrow-cons : {cons : ADTCons nₐ (k + suc ℓ)}
                → (Δ : CtxSuffix (suc ℓ) k)
                → All ((Γ , σ  ++ Δ) ⊢[ θ ]_) cons
                → All ((Γ , σ' ++ Δ) ⊢[ θ ]_) cons
    narrow-cons Δ [] = []
    narrow-cons Δ (δ ∷ consδs) = Γ⊢τ-narrowing Δ δ ∷ narrow-cons Δ consδs

  SVar-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                 → (Γ , σ ++ Δ) ok[ θ ]
                 → τ ∈ Γ , σ ++ Δ at ι
                 → Γ , σ' ++ Δ ⊢[ θ ] SVar ι ⦂ τ
  SVar-narrowing ⊘ (TCTX-Bind Γok τδ) (∈-zero refl) = T-Sub (T-Var (TCTX-Bind Γok Γ⊢σ') (∈-zero refl)) (Γ⊢τ-weakening Γok Γ⊢σ' τδ) (<:-weakening Γok Γ⊢σ' σ-<:)
  SVar-narrowing ⊘ (TCTX-Bind Γok _) (∈-suc refl ∈) = T-Var (TCTX-Bind Γok Γ⊢σ') (∈-suc refl ∈)
  SVar-narrowing (Δ , τ) Γ,σ,Δok (∈-zero refl) = T-Var (Γok-narrowing (Δ , _) Γ,σ,Δok) (∈-zero refl)
  SVar-narrowing (Δ , τ) (TCTX-Bind Γ,σ,Δok Γ,σ,Δ⊢τ) (∈-suc refl ∈)
    = let Γ,σ',Δok = Γok-narrowing Δ Γ,σ,Δok
          Γ,σ',Δ⊢τ = Γ⊢τ-narrowing Δ Γ,σ,Δ⊢τ
       in Γ⊢ε⦂τ-weakening Γ,σ',Δok Γ,σ',Δ⊢τ (SVar-narrowing Δ Γ,σ,Δok ∈)

  Γ⊢ε⦂τ-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                  → Γ , σ  ++ Δ ⊢[ θ ] ε ⦂ τ
                  → Γ , σ' ++ Δ ⊢[ θ ] ε ⦂ τ
  Γ⊢ε⦂τ-narrowing Δ (T-Unit Γok) = T-Unit (Γok-narrowing Δ Γok)
  Γ⊢ε⦂τ-narrowing Δ (T-Var Γok ∈) = SVar-narrowing Δ Γok ∈
  Γ⊢ε⦂τ-narrowing Δ (T-Abs arrδ εδ) = T-Abs (Γ⊢τ-narrowing Δ arrδ) (Γ⊢ε⦂τ-narrowing (Δ , _) εδ)
  Γ⊢ε⦂τ-narrowing Δ (T-App εδ εδ₁) = T-App (Γ⊢ε⦂τ-narrowing Δ εδ) (Γ⊢ε⦂τ-narrowing Δ εδ₁)
  Γ⊢ε⦂τ-narrowing Δ (T-Case resδ εδ branches-well-typed)
    = let resδ' = Γ⊢τ-narrowing Δ resδ
          εδ' = Γ⊢ε⦂τ-narrowing Δ εδ
       in T-Case resδ' εδ' (narrow-branches Δ branches-well-typed)
    where
    narrow-branches : ∀ {cons : ADTCons nₐ (k + suc ℓ)} {bs : CaseBranches nₐ (k + suc ℓ)}
                    → (Δ : CtxSuffix (suc ℓ) k)
                    → BranchesHaveType θ (Γ , σ  ++ Δ) cons bs τ
                    → BranchesHaveType θ (Γ , σ' ++ Δ) cons bs τ
    narrow-branches Δ NoBranches = NoBranches
    narrow-branches Δ (OneMoreBranch εδ bs) = OneMoreBranch (Γ⊢ε⦂τ-narrowing (Δ , _) εδ) (narrow-branches Δ bs)
  Γ⊢ε⦂τ-narrowing Δ (T-Con ≡-prf εδ adtτ) = T-Con ≡-prf (Γ⊢ε⦂τ-narrowing Δ εδ) (Γ⊢τ-narrowing Δ adtτ)
  Γ⊢ε⦂τ-narrowing Δ (T-Sub εδ τ'δ <:)
    = let εδ-narrowed = Γ⊢ε⦂τ-narrowing Δ εδ
          τ'δ-narrowed = Γ⊢τ-narrowing Δ τ'δ
          <:-narrowed = <:-narrowing Δ <:
       in T-Sub εδ-narrowed τ'δ-narrowed <:-narrowed
