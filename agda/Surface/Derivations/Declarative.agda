{-# OPTIONS --safe #-}

module Surface.Derivations.Declarative where

open import Data.Fin using (zero; suc)
open import Data.Maybe using (Is-just)
open import Data.Nat.Base using (_+_)
open import Data.Vec using (lookup; _∷_; [])
open import Data.Vec.Relation.Unary.All using (All; _∷_; []) public
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Common.Helpers

open import Surface.Syntax
open import Surface.Syntax.Substitution using ([_↦τ_]_; [_↦Γ_]_)
open import Surface.Syntax.Membership
import Surface.Syntax.Renaming as R
open import Surface.Oracle public
open import Surface.Derivations.Common public

data _ok[_]     : (Γ : Ctx ℓ) → Oracle → Set
data _⊢[_]_⦂_   (Γ : Ctx ℓ) (θ : Oracle) : (ε : STerm ℓ) → (τ : SType ℓ) → Set
data _⊢[_]_<:_  (Γ : Ctx ℓ) (θ : Oracle) : (τ τ' : SType ℓ) → Set
data _⊢[_]_     (Γ : Ctx ℓ) (θ : Oracle) : (τ : SType ℓ) → Set

infix 2 _⊢[_]_⦂_
infix 2 _⊢[_]_<:_
infix 1 _⊢[_]_

data BranchesHaveType (θ : Oracle) (Γ : Ctx ℓ)
                    : (cons : ADTCons nₐ ℓ)
                    → (bs : CaseBranches nₐ ℓ)
                    → (τ : SType ℓ)
                    → Set
                    where
  NoBranches    : BranchesHaveType θ Γ [] [] τ
  OneMoreBranch : ∀ {conτ} {cons' : ADTCons nₐ ℓ} {bs' : CaseBranches nₐ ℓ}
                → (εδ : (Γ , conτ) ⊢[ θ ] ε' ⦂ R.weaken-τ τ)
                → (rest : BranchesHaveType θ Γ cons' bs' τ)
                → BranchesHaveType θ Γ (conτ ∷ cons') (MkCaseBranch ε' ∷ bs') τ

data _ok[_] where
  TCTX-Empty : ⊘ ok[ θ ]
  TCTX-Bind  : (prevOk : Γ ok[ θ ])
             → (τδ : Γ ⊢[ θ ] τ)
             → (Γ , τ) ok[ θ ]

data _⊢[_]_ {ℓ} Γ θ where
  TWF-TrueRef : (Γok : Γ ok[ θ ])
              → Γ ⊢[ θ ] ⟨ b ∣ Τ ⟩
  TWF-Base    : (ε₁δ : Γ , ⟨ b ∣ Τ ⟩ ⊢[ θ ] ε₁ ⦂ ⟨ b' ∣ Τ ⟩)
              → (ε₂δ : Γ , ⟨ b ∣ Τ ⟩ ⊢[ θ ] ε₂ ⦂ ⟨ b' ∣ Τ ⟩)
              → Γ ⊢[ θ ] ⟨ b ∣ ε₁ ≈ ε₂ of ⟨ b' ∣ Τ ⟩ ⟩
  TWF-Conj    : (ρ₁δ : Γ ⊢[ θ ] ⟨ b ∣ ρ₁ ⟩)
              → (ρ₂δ : Γ ⊢[ θ ] ⟨ b ∣ ρ₂ ⟩)
              → Γ ⊢[ θ ] ⟨ b ∣ ρ₁ ∧ ρ₂ ⟩
  TWF-Arr     : (argδ : Γ ⊢[ θ ] τ₁)
              → (resδ : Γ , τ₁ ⊢[ θ ] τ₂)
              → Γ ⊢[ θ ] τ₁ ⇒ τ₂
  TWF-ADT     : {adtCons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → (consδs : All (Γ ⊢[ θ ]_) adtCons)
              → Γ ⊢[ θ ] ⊍ adtCons

data _⊢[_]_⦂_ {ℓ} Γ θ where
  T-Unit      : (Γok : Γ ok[ θ ])
              → Γ ⊢[ θ ] SUnit ⦂ ⟨ BUnit ∣ Τ ⟩
  T-Var       : (Γok : Γ ok[ θ ])
              → τ ∈ Γ at ι
              → Γ ⊢[ θ ] SVar ι ⦂ τ
  T-Abs       : (arrδ : Γ ⊢[ θ ] τ₁ ⇒ τ₂)
              → (bodyδ : Γ , τ₁ ⊢[ θ ] ε ⦂ τ₂)
              → Γ ⊢[ θ ] SLam τ₁ ε ⦂ τ₁ ⇒ τ₂
  T-App       : (δ₁ : Γ ⊢[ θ ] ε₁ ⦂ τ₁ ⇒ τ₂)
              → (δ₂ : Γ ⊢[ θ ] ε₂ ⦂ τ₁)
              → Γ ⊢[ θ ] SApp ε₁ ε₂ ⦂ [ zero ↦τ ε₂ ] τ₂
  T-Case      : {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → {bs : CaseBranches (Mkℕₐ (suc n)) ℓ}
              → (resδ : Γ ⊢[ θ ] τ)
              → (scrutτδ : Γ ⊢[ θ ] ε ⦂ ⊍ cons)
              → (branches-well-typed : BranchesHaveType θ Γ cons bs τ)
              → Γ ⊢[ θ ] SCase ε cons τ bs ⦂ τ
  T-Con       : ∀ {ι}
              → {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → (≡-prf : τⱼ ≡ lookup cons ι)
              → (conArg : Γ ⊢[ θ ] ε ⦂ τⱼ)
              → (adtτ : Γ ⊢[ θ ] ⊍ cons)
              → Γ ⊢[ θ ] SCon ι ε cons ⦂ ⊍ cons
  T-Sub       : (εδ : Γ ⊢[ θ ] ε ⦂ τ')
              → (τ'δ : Γ ⊢[ θ ] τ)
              → (<: : Γ ⊢[ θ ] τ' <: τ)
              → Γ ⊢[ θ ] ε ⦂ τ


data _⊢[_]_<:_ {ℓ} Γ θ where
  ST-Base : Is-just (Oracle.decide θ Γ b ρ₁ ρ₂)
          → Γ ⊢[ θ ] ⟨ b ∣ ρ₁ ⟩ <: ⟨ b ∣ ρ₂ ⟩
  ST-Arr  : Γ ⊢[ θ ] τ₁' <: τ₁
          → Γ , τ₁' ⊢[ θ ] τ₂' <: τ₂
          → Γ ⊢[ θ ] τ₁ ⇒ τ₂' <: τ₁' ⇒ τ₂
