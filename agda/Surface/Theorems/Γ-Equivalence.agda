{-# OPTIONS --safe #-}

module Surface.Theorems.Γ-Equivalence where

open import Data.Fin using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Membership
open import Surface.Derivations
open import Surface.Operational
open import Surface.Operational.BetaEquivalence
open import Surface.Theorems.Thinning

-- Referred to as context-equivalence in the paper
mutual
  <:-equivalence : (Δ : CtxSuffix (suc ℓ) k)
                 → τ ↭βτ τ'
                 → Γ ⊢ τ'
                 → Γ , τ  ++ Δ ⊢ τ₁ <: τ₂
                 → Γ , τ' ++ Δ ⊢ τ₁ <: τ₂
  <:-equivalence Δ τ-↭βτ Γ⊢τ' (ST-Base oracle is-just) = ST-Base oracle (Oracle.stepping oracle τ-↭βτ is-just)
  <:-equivalence Δ τ-↭βτ Γ⊢τ' (ST-Arr <:₁ <:₂ δτ₁⇒τ₂ δτ₁') = ST-Arr
                                                              (<:-equivalence Δ τ-↭βτ Γ⊢τ' <:₁)
                                                              (<:-equivalence (Δ , _) τ-↭βτ Γ⊢τ' <:₂)
                                                              (Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ' δτ₁⇒τ₂)
                                                              (Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ' δτ₁')

  Γok-equivalence : (Δ : CtxSuffix (suc ℓ) k)
                  → τ ↭βτ τ'
                  → Γ ⊢ τ'
                  → (Γ , τ  ++ Δ) ok
                  → (Γ , τ' ++ Δ) ok
  Γok-equivalence ⊘       τ-↭βτ Γ⊢τ' (TCTX-Bind Γok τδ) = TCTX-Bind Γok Γ⊢τ'
  Γok-equivalence (Δ , τ) τ-↭βτ Γ⊢τ' (TCTX-Bind Γok τδ) = TCTX-Bind (Γok-equivalence Δ τ-↭βτ Γ⊢τ' Γok) (Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ' τδ)

  Γ⊢τ-equivalence : (Δ : CtxSuffix (suc ℓ) k)
                  → τ₁ ↭βτ τ₁'
                  → Γ ⊢ τ₁'
                  → Γ , τ₁  ++ Δ ⊢ τ₂
                  → Γ , τ₁' ++ Δ ⊢ τ₂
  Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ' (TWF-TrueRef Γok) = TWF-TrueRef (Γok-equivalence Δ τ-↭βτ Γ⊢τ' Γok)
  Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ' (TWF-Base ε₁δ ε₂δ) = TWF-Base (Γ⊢ε⦂τ-equivalence (Δ , _) τ-↭βτ Γ⊢τ' ε₁δ) (Γ⊢ε⦂τ-equivalence (Δ , _) τ-↭βτ Γ⊢τ' ε₂δ)
  Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ' (TWF-Conj ρ₁δ ρ₂δ) = TWF-Conj (Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ' ρ₁δ) (Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ' ρ₂δ)
  Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ' (TWF-Arr argδ resδ) = TWF-Arr (Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ' argδ) (Γ⊢τ-equivalence (Δ , _) τ-↭βτ Γ⊢τ' resδ)
  Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ' (TWF-ADT consδs) = TWF-ADT (equiv-cons Δ τ-↭βτ Γ⊢τ' consδs)
    where
      equiv-cons : ∀ {cons : ADTCons nₐ (k + suc ℓ)}
                 → (Δ : CtxSuffix (suc ℓ) k)
                 → τ ↭βτ τ'
                 → Γ ⊢ τ'
                 → All ((Γ , τ  ++ Δ) ⊢_) cons
                 → All ((Γ , τ' ++ Δ) ⊢_) cons
      equiv-cons Δ τ-↭βτ Γ⊢τ' [] = []
      equiv-cons Δ τ-↭βτ Γ⊢τ' (δ ∷ consδs) = Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ' δ ∷ equiv-cons Δ τ-↭βτ Γ⊢τ' consδs

  Var-equivalence : (Δ : CtxSuffix (suc ℓ) k)
                  → τ₁ ↭βτ τ₁'
                  → Γ ⊢ τ₁'
                  → (Γ , τ₁ ++ Δ) ok
                  → τ ∈ Γ , τ₁ ++ Δ at ι
                  → Γ , τ₁' ++ Δ ⊢ SVar ι ⦂ τ
  Var-equivalence ⊘ τ-↭βτ Γ⊢τ₁' (TCTX-Bind ctx-ok τδ) (∈-zero refl)
    = let var-δ = T-Var (TCTX-Bind ctx-ok Γ⊢τ₁') (∈-zero refl)
          r-τδ = twf-weakening ctx-ok Γ⊢τ₁' τδ
          ↭βτ = ρ-preserves-↭βτ suc (↭βτ-is-symmetric τ-↭βτ)
       in T-RConv var-δ r-τδ ↭βτ
  Var-equivalence ⊘ τ-↭βτ Γ⊢τ₁' (TCTX-Bind ctx-ok τδ) (∈-suc refl ∈) = T-Var (TCTX-Bind ctx-ok Γ⊢τ₁') (∈-suc refl ∈)
  Var-equivalence (Δ , τ) τ-↭βτ Γ⊢τ₁' ctx-ok (∈-zero refl) = T-Var (Γok-equivalence (Δ , _) τ-↭βτ Γ⊢τ₁' ctx-ok) (∈-zero refl)
  Var-equivalence (Δ , τ) τ-↭βτ Γ⊢τ₁' (TCTX-Bind Γ,τ₁,Δ-ok τδ) (∈-suc refl ∈)
    = let Γ,τ₁',Δ-ok = Γok-equivalence Δ τ-↭βτ Γ⊢τ₁' Γ,τ₁,Δ-ok
          Γ,τ₁,Δ⊢τ = Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ₁' τδ
          SVar-ι = Var-equivalence Δ τ-↭βτ Γ⊢τ₁' Γ,τ₁,Δ-ok ∈
       in t-weakening Γ,τ₁',Δ-ok Γ,τ₁,Δ⊢τ SVar-ι

  Γ⊢ε⦂τ-equivalence : (Δ : CtxSuffix (suc ℓ) k)
                    → τ₁ ↭βτ τ₁'
                    → Γ ⊢ τ₁'
                    → Γ , τ₁  ++ Δ ⊢ ε ⦂ τ₂
                    → Γ , τ₁' ++ Δ ⊢ ε ⦂ τ₂
  Γ⊢ε⦂τ-equivalence Δ τ-↭βτ Γ⊢τ₁' (T-Unit Γok) = T-Unit (Γok-equivalence Δ τ-↭βτ Γ⊢τ₁' Γok)
  Γ⊢ε⦂τ-equivalence Δ τ-↭βτ Γ⊢τ₁' (T-Var Γok ∈) = Var-equivalence Δ τ-↭βτ Γ⊢τ₁' Γok ∈
  Γ⊢ε⦂τ-equivalence Δ τ-↭βτ Γ⊢τ₁' (T-Abs arrδ εδ) = T-Abs (Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ₁' arrδ) (Γ⊢ε⦂τ-equivalence (Δ , _) τ-↭βτ Γ⊢τ₁' εδ)
  Γ⊢ε⦂τ-equivalence Δ τ-↭βτ Γ⊢τ₁' (T-App ε₁δ ε₂δ) = T-App (Γ⊢ε⦂τ-equivalence Δ τ-↭βτ Γ⊢τ₁' ε₁δ) (Γ⊢ε⦂τ-equivalence Δ τ-↭βτ Γ⊢τ₁' ε₂δ)
  Γ⊢ε⦂τ-equivalence Δ τ-↭βτ Γ⊢τ₁' (T-Case resδ εδ branches-well-typed)
    = let resδ' = Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ₁' resδ
          εδ' = Γ⊢ε⦂τ-equivalence Δ τ-↭βτ Γ⊢τ₁' εδ
          branches-well-typed' = equiv-branches Δ τ-↭βτ Γ⊢τ₁' branches-well-typed
       in T-Case resδ' εδ' branches-well-typed'
    where
      equiv-branches : ∀ {cons : ADTCons nₐ (k + suc ℓ)} {bs : CaseBranches nₐ (k + suc ℓ)}
                     → (Δ : CtxSuffix (suc ℓ) k)
                     → τ ↭βτ τ'
                     → Γ ⊢ τ'
                     → BranchesHaveType (Γ , τ  ++ Δ) cons bs τ₀
                     → BranchesHaveType (Γ , τ' ++ Δ) cons bs τ₀
      equiv-branches Δ τ-↭βτ Γ⊢τ₁' NoBranches = NoBranches
      equiv-branches Δ τ-↭βτ Γ⊢τ₁' (OneMoreBranch εδ bs) = OneMoreBranch (Γ⊢ε⦂τ-equivalence (Δ , _) τ-↭βτ Γ⊢τ₁' εδ) (equiv-branches Δ τ-↭βτ Γ⊢τ₁' bs)
  Γ⊢ε⦂τ-equivalence Δ τ-↭βτ Γ⊢τ₁' (T-Con ≡-prf εδ adtτ) = T-Con ≡-prf (Γ⊢ε⦂τ-equivalence Δ τ-↭βτ Γ⊢τ₁' εδ) (Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ₁' adtτ)
  Γ⊢ε⦂τ-equivalence Δ τ-↭βτ Γ⊢τ₁' (T-Sub εδ τ'δ <:)
    = let εδ' = Γ⊢ε⦂τ-equivalence Δ τ-↭βτ Γ⊢τ₁' εδ
          τ'δ' = Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ₁' τ'δ
          <:' = <:-equivalence Δ τ-↭βτ Γ⊢τ₁' <:
       in T-Sub εδ' τ'δ' <:'
  Γ⊢ε⦂τ-equivalence Δ τ-↭βτ Γ⊢τ₁' (T-RConv εδ τ'δ τ~τ')
    = let εδ' = Γ⊢ε⦂τ-equivalence Δ τ-↭βτ Γ⊢τ₁' εδ
          τ'δ' = Γ⊢τ-equivalence Δ τ-↭βτ Γ⊢τ₁' τ'δ
       in T-RConv εδ' τ'δ' τ~τ'
