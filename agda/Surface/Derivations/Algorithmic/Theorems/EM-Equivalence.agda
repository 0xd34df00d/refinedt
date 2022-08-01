{-
The Enriched and the Minimal versions of the algorithmic type systems are equivalent.
-}

{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.EM-Equivalence where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Surface.Syntax
open import Surface.Syntax.Substitution
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
  to-M-ε (T-Abs εδ) = T-Abs (to-M-ε εδ)
  to-M-ε (T-App ε₁δ ε₂δ resτ-≡) = T-App (to-M-ε ε₁δ) (to-M-ε ε₂δ) resτ-≡
  to-M-ε (T-Case resδ εδ branchesδ) = T-Case (to-M-τ resδ) (to-M-ε εδ) (to-M-branches branchesδ)
  to-M-ε (T-Con ≡-prf εδ adtτ) = T-Con ≡-prf (to-M-ε εδ) (to-M-τ adtτ)
  to-M-ε (T-Sub εδ <:δ) = T-Sub (to-M-ε εδ) <:δ

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

mutual
  to-E-Γok : Γ ok[ θ , M ]
           → Γ ok[ θ , E ]
  to-E-Γok TCTX-Empty = TCTX-Empty
  to-E-Γok (TCTX-Bind Γok τδ) = TCTX-Bind (to-E-Γok Γok) (to-E-τ τδ)

  to-E-τ : Γ ⊢[ θ , M ] τ
         → Γ ⊢[ θ , E ] τ
  to-E-τ (TWF-TrueRef Γok) = TWF-TrueRef (to-E-Γok Γok)
  to-E-τ (TWF-Base ε₁δ ε₂δ) = TWF-Base (to-E-ε ε₁δ) (to-E-ε ε₂δ)
  to-E-τ (TWF-Conj τ₁δ τ₂δ) = TWF-Conj (to-E-τ τ₁δ) (to-E-τ τ₂δ)
  to-E-τ (TWF-Arr τ₁δ τ₂δ) = TWF-Arr (to-E-τ τ₁δ) (to-E-τ τ₂δ)
  to-E-τ (TWF-ADT consδs) = TWF-ADT (to-E-cons consδs)

  to-E-ε : Γ ⊢[ θ , M of κ ] ε ⦂ τ
         → Γ ⊢[ θ , E of κ ] ε ⦂ τ
  to-E-ε (T-Unit Γok) = T-Unit (to-E-Γok Γok)
  to-E-ε (T-Var Γok ∈) = T-Var (to-E-Γok Γok) ∈ ⦃ {! !} ⦄
  to-E-ε (T-Abs εδ) = T-Abs (to-E-ε εδ)
  to-E-ε (T-App ε₁δ ε₂δ refl ⦃ _ ⦄) = T-App (to-E-ε ε₁δ) (to-E-ε ε₂δ) refl ⦃ enriched {! !} ⦄
  to-E-ε (T-Case resδ εδ branchesδ) = T-Case (to-E-τ resδ) (to-E-ε εδ) (to-E-branches branchesδ)
  to-E-ε (T-Con ≡-prf εδ adtτ) = T-Con ≡-prf (to-E-ε εδ) (to-E-τ adtτ)
  to-E-ε (T-Sub εδ <:δ) = T-Sub (to-E-ε εδ) <:δ ⦃ {! !} ⦄

  to-E-cons : {cons : ADTCons nₐ ℓ}
            → All (Γ ⊢[ θ , M ]_) cons
            → All (Γ ⊢[ θ , E ]_) cons
  to-E-cons [] = []
  to-E-cons (τδ ∷ δs) = to-E-τ τδ ∷ to-E-cons δs

  to-E-branches : {cons : ADTCons nₐ ℓ}
                → {bs : CaseBranches nₐ ℓ}
                → BranchesHaveType θ M Γ cons bs τ
                → BranchesHaveType θ E Γ cons bs τ
  to-E-branches NoBranches = NoBranches
  to-E-branches (OneMoreBranch εδ branchesδ) = OneMoreBranch (to-E-ε εδ) (to-E-branches branchesδ)
