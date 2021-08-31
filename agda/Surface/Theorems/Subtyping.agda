{-# OPTIONS --safe #-}

module Surface.Theorems.Subtyping where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Membership
open import Surface.Derivations
open import Surface.Theorems.Thinning

-- Referred to as typing-narrowing in the paper
mutual
  <:-narrowing : ∀ Δ
               → Γ ⊢[ φ ] σ' <: σ
               → Enrich (Γ ⊢[ φ ] σ') φ
               → Γ , σ  ++ Δ ⊢[ φ ] τ₂ <: τ₂'
               → Γ , σ' ++ Δ ⊢[ φ ] τ₂ <: τ₂'
  <:-narrowing _ σ-<: [Γ⊢σ'] (ST-Base oracle is-just) = ST-Base oracle (Oracle.narrowing oracle {- TODO σ-<: -} is-just)
  <:-narrowing Δ σ-<: [Γ⊢σ'] (ST-Arr <:₁ <:₂ omitted omitted)
    = ST-Arr
        (<:-narrowing Δ σ-<: [Γ⊢σ'] <:₁)
        (<:-narrowing (Δ , _) σ-<: [Γ⊢σ'] <:₂)
        omitted
        omitted
  <:-narrowing Δ σ-<: (enriched Γ⊢σ') (ST-Arr <:₁ <:₂ (enriched δτ₁⇒τ₂) (enriched δτ₁'))
    = ST-Arr
        (<:-narrowing Δ σ-<: (enriched Γ⊢σ') <:₁)
        (<:-narrowing (Δ , _) σ-<: (enriched Γ⊢σ') <:₂)
        (enriched (Γ⊢τ-narrowing Δ σ-<: Γ⊢σ' δτ₁⇒τ₂))
        (enriched (Γ⊢τ-narrowing Δ σ-<: Γ⊢σ' δτ₁'))

  <:-trans : Γ ⊢[ φ ] τ₁ <: τ₂
           → Γ ⊢[ φ ] τ₂ <: τ₃
           → Γ ⊢[ φ ] τ₁ <: τ₃
  <:-trans (ST-Base oracle ⦃ UoO ⦄ is-just₁) (ST-Base oracle' is-just₂)
    rewrite UniquenessOfOracles.oracles-equal UoO oracle' oracle
          = ST-Base oracle ⦃ UoO ⦄ (Oracle.trans oracle is-just₁ is-just₂)
  <:-trans (ST-Arr <:₁ <:₂ δτ₁⇒τ₂ _) (ST-Arr <:₁' <:₂' _ δτ₁') = ST-Arr (<:-trans <:₁' <:₁) (<:-trans (<:-narrowing ⊘ <:₁' δτ₁' <:₂) <:₂') δτ₁⇒τ₂ δτ₁'

  Γok-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                → Γ ⊢[ φ ] σ' <: σ
                → Γ ⊢[ φ ] σ'
                → (Γ , σ  ++ Δ) ok[ φ ]
                → (Γ , σ' ++ Δ) ok[ φ ]
  Γok-narrowing ⊘ σ-<: Γ⊢σ' (TCTX-Bind Γok _) = TCTX-Bind Γok Γ⊢σ'
  Γok-narrowing (Δ , τ) σ-<: Γ⊢σ' (TCTX-Bind Γ,σ,Δok τδ) = TCTX-Bind (Γok-narrowing Δ σ-<: Γ⊢σ' Γ,σ,Δok) (Γ⊢τ-narrowing Δ σ-<: Γ⊢σ' τδ)

  Γ⊢τ-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                → Γ ⊢[ φ ] σ' <: σ
                → Γ ⊢[ φ ] σ'
                → Γ , σ  ++ Δ ⊢[ φ ] τ
                → Γ , σ' ++ Δ ⊢[ φ ] τ
  Γ⊢τ-narrowing Δ σ-<: Γ⊢σ' (TWF-TrueRef Γok) = TWF-TrueRef (Γok-narrowing Δ σ-<: Γ⊢σ' Γok)
  Γ⊢τ-narrowing Δ σ-<: Γ⊢σ' (TWF-Base ε₁δ ε₂δ) = TWF-Base (Γ⊢ε⦂τ-narrowing (Δ , _) σ-<: Γ⊢σ' ε₁δ) (Γ⊢ε⦂τ-narrowing (Δ , _) σ-<: Γ⊢σ' ε₂δ)
  Γ⊢τ-narrowing Δ σ-<: Γ⊢σ' (TWF-Conj ρ₁δ ρ₂δ) = TWF-Conj (Γ⊢τ-narrowing Δ σ-<: Γ⊢σ' ρ₁δ) (Γ⊢τ-narrowing Δ σ-<: Γ⊢σ' ρ₂δ)
  Γ⊢τ-narrowing Δ σ-<: Γ⊢σ' (TWF-Arr argδ resδ) = TWF-Arr (Γ⊢τ-narrowing Δ σ-<: Γ⊢σ' argδ) (Γ⊢τ-narrowing (Δ , _) σ-<: Γ⊢σ' resδ)
  Γ⊢τ-narrowing {φ = φ} Δ σ-<: Γ⊢σ' (TWF-ADT consδs) = TWF-ADT (narrow-cons Δ σ-<: Γ⊢σ' consδs)
    where
      narrow-cons : {cons : ADTCons nₐ (k + suc ℓ)}
                  → (Δ : CtxSuffix (suc ℓ) k)
                  → Γ ⊢[ φ ] σ' <: σ
                  → Γ ⊢[ φ ] σ'
                  → All ((Γ , σ  ++ Δ) ⊢[ φ ]_) cons
                  → All ((Γ , σ' ++ Δ) ⊢[ φ ]_) cons
      narrow-cons Δ _ _ [] = []
      narrow-cons Δ σ-<: Γ⊢σ' (δ ∷ consδs) = Γ⊢τ-narrowing Δ σ-<: Γ⊢σ' δ ∷ narrow-cons Δ σ-<: Γ⊢σ' consδs

  SVar-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                 → (Γ , σ ++ Δ) ok[ φ ]
                 → Γ ⊢[ φ ] σ' <: σ
                 → Γ ⊢[ φ ] σ'
                 → τ ∈ Γ , σ ++ Δ at ι
                 → Γ , σ' ++ Δ ⊢[ φ ] SVar ι ⦂ τ
  SVar-narrowing ⊘ (TCTX-Bind Γok τδ) σ-<: Γ⊢σ' (∈-zero refl) = T-Sub (T-Var (TCTX-Bind Γok Γ⊢σ') (∈-zero refl)) (Γ⊢τ-weakening Γok Γ⊢σ' τδ) (<:-weakening Γok Γ⊢σ' σ-<:)
  SVar-narrowing ⊘ (TCTX-Bind Γok _) σ-<: Γ⊢σ' (∈-suc refl ∈) = T-Var (TCTX-Bind Γok Γ⊢σ') (∈-suc refl ∈)
  SVar-narrowing (Δ , τ) Γ,σ,Δok σ-<: Γ⊢σ' (∈-zero refl) = T-Var (Γok-narrowing (Δ , _) σ-<: Γ⊢σ' Γ,σ,Δok) (∈-zero refl)
  SVar-narrowing (Δ , τ) (TCTX-Bind Γ,σ,Δok Γ,σ,Δ⊢τ) σ-<: Γ⊢σ' (∈-suc refl ∈)
    = let Γ,σ',Δok = Γok-narrowing Δ σ-<: Γ⊢σ' Γ,σ,Δok
          Γ,σ',Δ⊢τ = Γ⊢τ-narrowing Δ σ-<: Γ⊢σ' Γ,σ,Δ⊢τ
       in Γ⊢ε⦂τ-weakening Γ,σ',Δok Γ,σ',Δ⊢τ (SVar-narrowing Δ Γ,σ,Δok σ-<: Γ⊢σ' ∈)

  Γ⊢ε⦂τ-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                  → Γ ⊢[ φ ] σ' <: σ
                  → Γ ⊢[ φ ] σ'
                  → Γ , σ  ++ Δ ⊢[ φ ] ε ⦂ τ
                  → Γ , σ' ++ Δ ⊢[ φ ] ε ⦂ τ
  Γ⊢ε⦂τ-narrowing Δ σ-<: Γ⊢σ' (T-Unit Γok) = T-Unit (Γok-narrowing Δ σ-<: Γ⊢σ' Γok)
  Γ⊢ε⦂τ-narrowing Δ σ-<: Γ⊢σ' (T-Var Γok ∈) = SVar-narrowing Δ Γok σ-<: Γ⊢σ' ∈
  Γ⊢ε⦂τ-narrowing Δ σ-<: Γ⊢σ' (T-Abs arrδ εδ) = T-Abs (Γ⊢τ-narrowing Δ σ-<: Γ⊢σ' arrδ) (Γ⊢ε⦂τ-narrowing (Δ , _) σ-<: Γ⊢σ' εδ)
  Γ⊢ε⦂τ-narrowing Δ σ-<: Γ⊢σ' (T-App εδ εδ₁) = T-App (Γ⊢ε⦂τ-narrowing Δ σ-<: Γ⊢σ' εδ) (Γ⊢ε⦂τ-narrowing Δ σ-<: Γ⊢σ' εδ₁)
  Γ⊢ε⦂τ-narrowing {φ = φ} Δ σ-<: Γ⊢σ' (T-Case resδ εδ branches-well-typed)
    = let resδ' = Γ⊢τ-narrowing Δ σ-<: Γ⊢σ' resδ
          εδ' = Γ⊢ε⦂τ-narrowing Δ σ-<: Γ⊢σ' εδ
       in T-Case resδ' εδ' (narrow-branches Δ σ-<: Γ⊢σ' branches-well-typed)
    where
      narrow-branches : ∀ {cons : ADTCons nₐ (k + suc ℓ)} {bs : CaseBranches nₐ (k + suc ℓ)}
                      → (Δ : CtxSuffix (suc ℓ) k)
                      → Γ ⊢[ φ ] σ' <: σ
                      → Γ ⊢[ φ ] σ'
                      → BranchesHaveType φ (Γ , σ  ++ Δ) cons bs τ
                      → BranchesHaveType φ (Γ , σ' ++ Δ) cons bs τ
      narrow-branches Δ σ-<: Γ⊢σ' NoBranches = NoBranches
      narrow-branches Δ σ-<: Γ⊢σ' (OneMoreBranch εδ bs) = OneMoreBranch (Γ⊢ε⦂τ-narrowing (Δ , _) σ-<: Γ⊢σ' εδ) (narrow-branches Δ σ-<: Γ⊢σ' bs)
  Γ⊢ε⦂τ-narrowing Δ σ-<: Γ⊢σ' (T-Con ≡-prf εδ adtτ) = T-Con ≡-prf (Γ⊢ε⦂τ-narrowing Δ σ-<: Γ⊢σ' εδ) (Γ⊢τ-narrowing Δ σ-<: Γ⊢σ' adtτ)
  Γ⊢ε⦂τ-narrowing Δ σ-<: Γ⊢σ' (T-Sub εδ τ'δ <:)
    = let εδ-narrowed = Γ⊢ε⦂τ-narrowing Δ σ-<: Γ⊢σ' εδ
          τ'δ-narrowed = Γ⊢τ-narrowing Δ σ-<: Γ⊢σ' τ'δ
          <:-narrowed = <:-narrowing Δ σ-<: (as-enrichment Γ⊢σ') <:
       in T-Sub εδ-narrowed τ'δ-narrowed <:-narrowed
