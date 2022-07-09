{-
The Enriched and the Minimal versions of the algorithmic type systems are equivalent.
-}

{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.EM-Equivalence where

open import Function.Inverse

open import Surface.Syntax
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Agreement

mutual
  to-M-Γok : Γ ok[ θ , E ]
           → Γ ok[ θ , M ]
  to-M-Γok TCTX-Empty = TCTX-Empty
  to-M-Γok (TCTX-Bind Γok τδ) = TCTX-Bind (to-M-Γok Γok) (to-M-τ τδ)

  to-M-τ : Γ ⊢[ θ , E ] τ
         → Γ ⊢[ θ , M ] τ
  to-M-τ (TWF-TrueRef Γok) = TWF-TrueRef (to-M-Γok Γok)
  to-M-τ (TWF-Base ε₁δ ε₂δ) = TWF-Base (to-M-ε ε₁δ) (to-M-ε ε₂δ)
  to-M-τ (TWF-Conj τ₁δ τ₂δ) = TWF-Conj (to-M-τ τ₁δ) (to-M-τ τ₂δ)
  to-M-τ (TWF-Arr τ₁δ τ₂δ) = TWF-Arr (to-M-τ τ₁δ) (to-M-τ τ₂δ)
  to-M-τ (TWF-ADT consδs) = TWF-ADT (to-M-cons consδs)
                
  to-M-ε : Γ ⊢[ θ , E of κ ] ε ⦂ τ
         → Γ ⊢[ θ , M of κ ] ε ⦂ τ
  to-M-ε (T-Unit Γok) = T-Unit (to-M-Γok Γok)
  to-M-ε (T-Var Γok ∈) = T-Var (to-M-Γok Γok) ∈
  to-M-ε (T-Abs arrδ εδ) = T-Abs (to-M-τ arrδ) (to-M-ε εδ)
  to-M-ε (T-App ε₁δ ε₂δ resτ-≡ resτδ) = T-App (to-M-ε ε₁δ) (to-M-ε ε₂δ) resτ-≡ (to-M-τ resτδ)
  to-M-ε (T-Case resδ εδ branchesδ) = T-Case (to-M-τ resδ) (to-M-ε εδ) (to-M-branches branchesδ)
  to-M-ε (T-Con ≡-prf εδ adtτ) = T-Con ≡-prf (to-M-ε εδ) (to-M-τ adtτ)
  to-M-ε (T-Sub εδ τδ <:δ) = T-Sub (to-M-ε εδ) (to-M-τ τδ) (to-M-<: <:δ)

  to-M-<: : Γ ⊢[ θ , E ] τ' <: τ
          → Γ ⊢[ θ , M ] τ' <: τ
  to-M-<: (ST-Base is-just _ _) = ST-Base is-just omitted omitted
  to-M-<: (ST-Arr <:₁δ <:₂δ _ _) = ST-Arr (to-M-<: <:₁δ) (to-M-<: <:₂δ) omitted omitted
  to-M-<: (ST-ADT _) = ST-ADT omitted

  to-M-cons : {cons : ADTCons nₐ ℓ}
            → All (Γ ⊢[ θ , E ]_) cons
            → All (Γ ⊢[ θ , M ]_) cons
  to-M-cons [] = []
  to-M-cons (τδ ∷ δs) = to-M-τ τδ ∷ to-M-cons δs

  to-M-branches : {cons : ADTCons nₐ ℓ}
                → {bs : CaseBranches nₐ ℓ}
                → BranchesHaveType θ E Γ cons bs τ
                → BranchesHaveType θ M Γ cons bs τ
  to-M-branches NoBranches = NoBranches
  to-M-branches (OneMoreBranch εδ branchesδ) = OneMoreBranch (to-M-ε εδ) (to-M-branches branchesδ)
