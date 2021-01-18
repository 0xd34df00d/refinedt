module Surface.Theorems.Γ-Equivalence where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.WellScoped
open import Surface.WellScoped.CtxSuffix
open import Surface.WellScoped.Membership
open import Surface.Derivations
open import Surface.Operational
open import Surface.Operational.BetaEquivalence

<:-equivalence : (Δ : CtxSuffix (suc ℓ) k)
               → τ ≡rβ τ'
               → Γ , τ  ++ Δ ⊢ τ₁ <: τ₂
               → Γ , τ' ++ Δ ⊢ τ₁ <: τ₂
<:-equivalence Δ τ-≡rβ (ST-Base oracle is-just) = ST-Base oracle {! !}
<:-equivalence Δ τ-≡rβ (ST-Arr <:₁ <:₂) = ST-Arr (<:-equivalence Δ τ-≡rβ <:₁) (<:-equivalence (Δ , _) τ-≡rβ <:₂)

mutual
  Γok-equivalence : (Δ : CtxSuffix (suc ℓ) k)
                  → τ ≡rβ τ'
                  → Γ ⊢ τ'
                  → (Γ , τ  ++ Δ) ok
                  → (Γ , τ' ++ Δ) ok
  Γok-equivalence ⊘       τ-≡rβ Γ⊢τ' (TCTX-Bind Γok τδ) = TCTX-Bind Γok Γ⊢τ'
  Γok-equivalence (Δ , τ) τ-≡rβ Γ⊢τ' (TCTX-Bind Γok τδ) = TCTX-Bind (Γok-equivalence Δ τ-≡rβ Γ⊢τ' Γok) (Γ⊢τ-equivalence Δ τ-≡rβ Γ⊢τ' τδ)

  Γ⊢τ-equivalence : (Δ : CtxSuffix (suc ℓ) k)
                  → τ₁ ≡rβ τ₁'
                  → Γ ⊢ τ₁'
                  → Γ , τ₁  ++ Δ ⊢ τ₂
                  → Γ , τ₁' ++ Δ ⊢ τ₂
  Γ⊢τ-equivalence Δ τ-≡rβ Γ⊢τ' (TWF-TrueRef Γok) = TWF-TrueRef (Γok-equivalence Δ τ-≡rβ Γ⊢τ' Γok)
  Γ⊢τ-equivalence Δ τ-≡rβ Γ⊢τ' (TWF-Base ε₁δ ε₂δ) = TWF-Base (Γ⊢ε⦂τ-equivalence (Δ , _) τ-≡rβ Γ⊢τ' ε₁δ) (Γ⊢ε⦂τ-equivalence (Δ , _) τ-≡rβ Γ⊢τ' ε₂δ)
  Γ⊢τ-equivalence Δ τ-≡rβ Γ⊢τ' (TWF-Conj ρ₁δ ρ₂δ) = TWF-Conj (Γ⊢τ-equivalence Δ τ-≡rβ Γ⊢τ' ρ₁δ) (Γ⊢τ-equivalence Δ τ-≡rβ Γ⊢τ' ρ₂δ)
  Γ⊢τ-equivalence Δ τ-≡rβ Γ⊢τ' (TWF-Arr argδ resδ) = TWF-Arr (Γ⊢τ-equivalence Δ τ-≡rβ Γ⊢τ' argδ) (Γ⊢τ-equivalence (Δ , _) τ-≡rβ Γ⊢τ' resδ)
  Γ⊢τ-equivalence Δ τ-≡rβ Γ⊢τ' (TWF-ADT consδs) = TWF-ADT (equiv-cons Δ τ-≡rβ Γ⊢τ' consδs)
    where
      equiv-cons : ∀ {cons : ADTCons nₐ (k + suc ℓ)}
                 → (Δ : CtxSuffix (suc ℓ) k)
                 → τ ≡rβ τ'
                 → Γ ⊢ τ'
                 → All ((Γ , τ  ++ Δ) ⊢_) cons
                 → All ((Γ , τ' ++ Δ) ⊢_) cons
      equiv-cons Δ τ-≡rβ Γ⊢τ' [] = []
      equiv-cons Δ τ-≡rβ Γ⊢τ' (δ ∷ consδs) = Γ⊢τ-equivalence Δ τ-≡rβ Γ⊢τ' δ ∷ equiv-cons Δ τ-≡rβ Γ⊢τ' consδs

  Γ⊢ε⦂τ-equivalence : (Δ : CtxSuffix (suc ℓ) k)
                    → τ₁ ≡rβ τ₁'
                    → Γ ⊢ τ₁'
                    → Γ , τ₁  ++ Δ ⊢ ε ⦂ τ₂
                    → Γ , τ₁' ++ Δ ⊢ ε ⦂ τ₂
  Γ⊢ε⦂τ-equivalence Δ τ-≡rβ Γ⊢τ₁' (T-Unit Γok) = T-Unit (Γok-equivalence Δ τ-≡rβ Γ⊢τ₁' Γok)
  Γ⊢ε⦂τ-equivalence Δ τ-≡rβ Γ⊢τ₁' (T-Var Γok ∈) = {! !}
  Γ⊢ε⦂τ-equivalence Δ τ-≡rβ Γ⊢τ₁' (T-Abs arrδ εδ) = T-Abs (Γ⊢τ-equivalence Δ τ-≡rβ Γ⊢τ₁' arrδ) (Γ⊢ε⦂τ-equivalence (Δ , _) τ-≡rβ Γ⊢τ₁' εδ)
  Γ⊢ε⦂τ-equivalence Δ τ-≡rβ Γ⊢τ₁' (T-App ε₁δ ε₂δ) = T-App (Γ⊢ε⦂τ-equivalence Δ τ-≡rβ Γ⊢τ₁' ε₁δ) (Γ⊢ε⦂τ-equivalence Δ τ-≡rβ Γ⊢τ₁' ε₂δ)
  Γ⊢ε⦂τ-equivalence Δ τ-≡rβ Γ⊢τ₁' (T-Case resδ εδ branches-well-typed)
    = let resδ' = Γ⊢τ-equivalence Δ τ-≡rβ Γ⊢τ₁' resδ
          εδ' = Γ⊢ε⦂τ-equivalence Δ τ-≡rβ Γ⊢τ₁' εδ
          branches-well-typed' = equiv-branches Δ τ-≡rβ Γ⊢τ₁' branches-well-typed
       in T-Case resδ' εδ' branches-well-typed'
    where
      equiv-branches : ∀ {cons : ADTCons nₐ (k + suc ℓ)} {bs : CaseBranches nₐ (k + suc ℓ)}
                     → (Δ : CtxSuffix (suc ℓ) k)
                     → τ ≡rβ τ'
                     → Γ ⊢ τ'
                     → BranchesHaveType (Γ , τ  ++ Δ) cons bs τ₀
                     → BranchesHaveType (Γ , τ' ++ Δ) cons bs τ₀
      equiv-branches Δ τ-≡rβ Γ⊢τ₁' NoBranches = NoBranches
      equiv-branches Δ τ-≡rβ Γ⊢τ₁' (OneMoreBranch εδ bs) = OneMoreBranch (Γ⊢ε⦂τ-equivalence (Δ , _) τ-≡rβ Γ⊢τ₁' εδ) (equiv-branches Δ τ-≡rβ Γ⊢τ₁' bs)
  Γ⊢ε⦂τ-equivalence Δ τ-≡rβ Γ⊢τ₁' (T-Con ≡-prf εδ adtτ) = T-Con ≡-prf (Γ⊢ε⦂τ-equivalence Δ τ-≡rβ Γ⊢τ₁' εδ) (Γ⊢τ-equivalence Δ τ-≡rβ Γ⊢τ₁' adtτ)
  Γ⊢ε⦂τ-equivalence Δ τ-≡rβ Γ⊢τ₁' (T-Sub εδ τ'δ <:)
    = let εδ' = Γ⊢ε⦂τ-equivalence Δ τ-≡rβ Γ⊢τ₁' εδ
          τ'δ' = Γ⊢τ-equivalence Δ τ-≡rβ Γ⊢τ₁' τ'δ
          <:' = <:-equivalence Δ τ-≡rβ <:
       in T-Sub εδ' τ'δ' <:'
  Γ⊢ε⦂τ-equivalence Δ τ-≡rβ Γ⊢τ₁' (T-RConv εδ τ'δ τ~τ')
    = let εδ' = Γ⊢ε⦂τ-equivalence Δ τ-≡rβ Γ⊢τ₁' εδ
          τ'δ' = Γ⊢τ-equivalence Δ τ-≡rβ Γ⊢τ₁' τ'δ
       in T-RConv εδ' τ'δ' τ~τ'
