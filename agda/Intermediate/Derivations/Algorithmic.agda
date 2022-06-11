{-# OPTIONS --safe #-}

module Intermediate.Derivations.Algorithmic where

open import Data.Fin using (zero; suc)
open import Data.Maybe using (Is-just)
open import Data.Vec using (lookup; _∷_; [])
open import Data.Vec.Relation.Unary.All using (All; _∷_; []) public
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Common.Helpers

open import Intermediate.Oracle public
open import Intermediate.Syntax
open import Intermediate.Syntax.Membership
open import Intermediate.Syntax.Substitution using ([_↦τ_]_; [_↦ρ<_]_)
import Intermediate.Syntax.Renaming as R

data [_]_ok     (Θ : Oracle) : (Γ : Ctx ℓ) → Set
data [_]_⊢_⦂_   (θ : Oracle) (Γ : Ctx ℓ) : (ε : ITerm ℓ) → (τ : IType ℓ) → Set
data [_]_⊢_<:_  (θ : Oracle) (Γ : Ctx ℓ) : (τ τ' : IType ℓ) → Set
data [_]_⊢_     (θ : Oracle) (Γ : Ctx ℓ) : (τ : IType ℓ) → Set

infix 2 [_]_⊢_⦂_
infix 2 [_]_⊢_<:_
infix 1 [_]_⊢_

data BranchesHaveType (θ : Oracle) (Γ : Ctx ℓ)
                    : (cons : ADTCons nₐ ℓ)
                    → (bs : CaseBranches nₐ ℓ)
                    → (τ' : IType ℓ)
                    → Set
                    where
  NoBranches    : BranchesHaveType θ Γ [] [] τ'
  OneMoreBranch : ∀ {conτ} {cons' : ADTCons nₐ ℓ} {bs' : CaseBranches nₐ ℓ}
                → (εδ : [ θ ] (Γ , conτ) ⊢ ε' ⦂ R.weaken-τ τ')
                → (rest : BranchesHaveType θ Γ cons' bs' τ')
                → BranchesHaveType θ Γ (conτ ∷ cons') (MkCaseBranch ε' ∷ bs') τ'

data [_]_ok θ where
  TCTX-Empty : [ θ ] ⊘ ok
  TCTX-Bind  : (prevOk : [ θ ] Γ ok)
             → (τδ : [ θ ] Γ ⊢ τ)
             → [ θ ] (Γ , τ) ok

data [_]_⊢_ {ℓ} θ Γ where
  TWF-TrueRef : (Γok : [ θ ] Γ ok)
              → [ θ ] Γ ⊢ ⟨ b ∣ Τ ⟩
  TWF-Base    : (ε₁δ : [ θ ] Γ , ⟨ b ∣ Τ ⟩ ⊢ ε₁ ⦂ ⟨ b' ∣ Τ ⟩)
              → (ε₂δ : [ θ ] Γ , ⟨ b ∣ Τ ⟩ ⊢ ε₂ ⦂ ⟨ b' ∣ Τ ⟩)
              → [ θ ] Γ ⊢ ⟨ b ∣ ε₁ ≈ ε₂ of ⟨ b' ∣ Τ ⟩ ⟩
  TWF-Conj    : (ρ₁δ : [ θ ] Γ ⊢ ⟨ b ∣ ρ₁ ⟩)
              → (ρ₂δ : [ θ ] Γ ⊢ ⟨ b ∣ ρ₂ ⟩)
              → [ θ ] Γ ⊢ ⟨ b ∣ ρ₁ ∧ ρ₂ ⟩
  TWF-Arr     : (argδ : [ θ ] Γ ⊢ τ₁)
              → (resδ : [ θ ] Γ , τ₁ ⊢ τ₂)
              → [ θ ] Γ ⊢ τ₁ ⇒ τ₂
  TWF-ADT     : {adtCons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → (consδs : All ([ θ ] Γ ⊢_) adtCons)
              → [ θ ] Γ ⊢ ⊍ adtCons

data [_]_⊢_⦂_ {ℓ} θ Γ where
  T-Unit      : (Γok : [ θ ] Γ ok)
              → [ θ ] Γ ⊢ IUnit ⦂ ⟨ BUnit ∣ Τ ⟩
  T-Var       : (Γok : [ θ ] Γ ok)
              → τ ∈ Γ at ι
              → [ θ ] Γ ⊢ IVar ι ⦂ τ
  T-Abs       : (arrδ : [ θ ] Γ ⊢ τ₁ ⇒ τ₂)
              → (bodyδ : [ θ ] Γ , τ₁ ⊢ ε ⦂ τ₂)
              → [ θ ] Γ ⊢ ILam τ₁ ε ⦂ τ₁ ⇒ τ₂
  T-App       : (δ₁ : [ θ ] Γ ⊢ ε₁ ⦂ τ₁ ⇒ τ₂)
              → (δ₂ : [ θ ] Γ ⊢ ε₂ ⦂ τ₁)
              → (resτ-≡ : τ ≡ [ zero ↦τ ε₂ ] τ₂)
              → (resτδ : [ θ ] Γ ⊢ τ)
              → [ θ ] Γ ⊢ IApp ε₁ ε₂ ⦂ τ
  T-Case      : {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → {bs : CaseBranches (Mkℕₐ (suc n)) ℓ}
              → (resδ : [ θ ] Γ ⊢ τ')
              → (scrutτδ : [ θ ] Γ ⊢ ε ⦂ ⊍ cons)
              → (branches-well-typed : BranchesHaveType θ Γ cons bs τ')
              → [ θ ] Γ ⊢ ICase ε bs ⦂ τ'
  T-Con       : ∀ {ι}
              → {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → (≡-prf : τⱼ ≡ lookup cons ι)
              → (conArg : [ θ ] Γ ⊢ ε ⦂ τⱼ)
              → (adtτ : [ θ ] Γ ⊢ ⊍ cons)
              → [ θ ] Γ ⊢ ICon ι ε cons ⦂ ⊍ cons
  T-SubW      : (<: : [ θ ] Γ ⊢ τ' <: τ)
              → (εδ : [ θ ] Γ ⊢ ε ⦂ τ')
              → [ θ ] Γ ⊢ ε I<: τ ⦂ τ

data [_]_⊢_<:_ {ℓ} θ Γ where
  ST-Base : Is-just (Oracle.decide θ Γ b ρ₁ ρ₂)
          → (ρ₁δ : [ θ ] Γ ⊢ ⟨ b ∣ ρ₁ ⟩)
          → (ρ₂δ : [ θ ] Γ ⊢ ⟨ b ∣ ρ₂ ⟩)
          → [ θ ] Γ ⊢ ⟨ b ∣ ρ₁ ⟩ <: ⟨ b ∣ ρ₂ ⟩
  ST-Arr  : (<:₁δ : [ θ ] Γ ⊢ τ₁' <: τ₁)
          → (<:₂δ : [ θ ] Γ , τ₁' ⊢ τ₂' <: τ₂)
          → (τ₁⇒τ₂'δ : [ θ ] Γ ⊢ τ₁  ⇒ τ₂')
          → (τ₁'⇒τ₂δ : [ θ ] Γ ⊢ τ₁' ⇒ τ₂)
          → [ θ ] Γ ⊢ τ₁ ⇒ τ₂' <: τ₁' ⇒ τ₂

variable
  θ : Oracle
