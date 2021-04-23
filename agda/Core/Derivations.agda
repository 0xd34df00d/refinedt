{-# OPTIONS --safe #-}

module Core.Derivations where

open import Data.Fin using (zero)
open import Data.Vec using (lookup; _∷_; [])
open import Data.Vec.Relation.Unary.All using (All; _∷_; []) public
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Core.Syntax
open import Core.Syntax.Renaming
open import Core.Syntax.Substitution
open import Core.Operational

data _=β_ : CExpr ℓ → CExpr ℓ → Set where
  =-witness : ∀ ε
            → ε₁ ↝⋆ ε
            → ε₂ ↝⋆ ε
            → ε₁ =β ε₂

infix 2 _⊢_⦂_
data _⊢_⦂_ : Ctx ℓ → CExpr ℓ → CExpr ℓ → Set

data BranchesHaveType (Γ : Ctx ℓ) (ε : CExpr ℓ)
    : (cons : ADTCons nₐ ℓ)
    → (bs : CaseBranches nₐ ℓ)
    → (τ' : CExpr ℓ)
    → Set
    where
  NoBranches : BranchesHaveType Γ ε [] [] τ'
  OneMoreBranch : ∀ {conτ} {cons' : ADTCons nₐ ℓ} {bs' : CaseBranches nₐ ℓ}
                → (εδ : (Γ , conτ , {! !}) ⊢ ε' ⦂ weaken-ε-k 2 τ')
                → (rest : BranchesHaveType Γ ε cons' bs' τ')
                → BranchesHaveType Γ ε (conτ ∷ cons') (ε' ∷ bs') τ'

data _⊢_⦂_ where
  -- Base λC
  CT-Sort : ⊘ ⊢ ⋆ₑ ⦂ □ₑ
  CT-Var : Γ ⊢ τ ⦂ CSort s
         → Γ , τ ⊢ CVar zero ⦂ weaken-ε τ
  CT-Weaken : Γ ⊢ ε₁ ⦂ τ₁
            → Γ ⊢ τ₂ ⦂ CSort s
            → Γ , τ₂ ⊢ weaken-ε ε₁ ⦂ weaken-ε τ₁
  CT-Form : Γ ⊢ τ₁ ⦂ CSort s₁
          → Γ , τ₁ ⊢ τ₂ ⦂ CSort s₂
          → Γ ⊢ CΠ τ₁ τ₂ ⦂ CSort s₂
  CT-App : Γ ⊢ ε₁ ⦂ CΠ τ₁ τ₂
         → Γ ⊢ ε₂ ⦂ τ₁
         → Γ ⊢ ε₁ · ε₂ ⦂ [ zero ↦ ε₂ ] τ₂
  CT-Abs : Γ , τ₁ ⊢ ε ⦂ τ₂
         → Γ ⊢ CΠ τ₁ τ₂ ⦂ CSort s
         → Γ ⊢ CLam τ₁ ε ⦂ CΠ τ₁ τ₂
  CT-Conv : Γ ⊢ ε ⦂ τ₁
          → Γ ⊢ τ₂ ⦂ CSort s
          → τ₁ =β τ₂
          → Γ ⊢ ε ⦂ τ₂

  -- Our extensions
  CT-UnitType : Γ ⊢ ⋆ₑ ⦂ □ₑ
              → Γ ⊢ CUnit ⦂ ⋆ₑ
  CT-UnitTerm : Γ ⊢ ⋆ₑ ⦂ □ₑ
              → Γ ⊢ Cunit ⦂ CUnit
  CT-ADTForm : {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
             → (consδs : All (λ con → Γ ⊢ con ⦂ ⋆ₑ) cons)
             → Γ ⊢ CADT cons ⦂ ⋆ₑ
  CT-ADTCon : ∀ {ι}
            → {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
            → (≡-prf : τⱼ ≡ lookup cons ι)
            → (conArg : Γ ⊢ ε ⦂ τⱼ)
            → (adtτ : Γ ⊢ CADT cons ⦂ ⋆ₑ)
            → Γ ⊢ CCon ι ε cons ⦂ CADT cons
  CT-ADTCase : {bs : CaseBranches (Mkℕₐ (suc n)) ℓ}
             → {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
             → (τ'δ : Γ ⊢ τ' ⦂ ⋆ₑ)
             → (εδ : Γ ⊢ ε ⦂ CADT cons)
             → (branches : BranchesHaveType Γ ε cons bs τ')
             → Γ ⊢ CCase ε bs ⦂ τ'
