{-# OPTIONS --safe #-}

module Intermediate.Derivations.Algorithmic where

open import Data.Fin using (zero; suc)
open import Data.Maybe
open import Data.Nat.Base using (_+_)
open import Data.Vec using (lookup; _∷_; [])
open import Data.Vec.Relation.Unary.All using (All; _∷_; []) public
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Common.Helpers

open import Intermediate.Syntax
open import Intermediate.Syntax.CtxSuffix
open import Intermediate.Syntax.Membership
open import Intermediate.Syntax.Subcontext
open import Intermediate.Syntax.Substitution using ([_↦τ_]_)
import Intermediate.Syntax.Renaming as R
import Intermediate.Syntax.Substitution as S

open import Core.Syntax using (CExpr)
open import Core.Syntax.Renaming as CR using (act-ε)

record Oracle : Set

data [_]_ok     (Θ : Oracle) : (Γ : Ctx ℓ) → Set
data [_]_⊢_⦂_   (θ : Oracle) (Γ : Ctx ℓ) : (ε : STerm ℓ) → (τ : SType ℓ) → Set
data [_]_⊢_<:_  (θ : Oracle) (Γ : Ctx ℓ) : (τ τ' : SType ℓ) → Set
data [_]_⊢_     (θ : Oracle) (Γ : Ctx ℓ) : (τ : SType ℓ) → Set

infix 2 [_]_⊢_⦂_
infix 2 [_]_⊢_<:_
infix 1 [_]_⊢_

data BranchesHaveType (θ : Oracle) (Γ : Ctx ℓ)
                    : (cons : ADTCons nₐ ℓ)
                    → (bs : CaseBranches nₐ ℓ)
                    → (τ' : SType ℓ)
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
              → [ θ ] Γ ⊢ SUnit ⦂ ⟨ BUnit ∣ Τ ⟩
  T-Var       : (Γok : [ θ ] Γ ok)
              → τ ∈ Γ at ι
              → [ θ ] Γ ⊢ SVar ι ⦂ τ
  T-Abs       : (arrδ : [ θ ] Γ ⊢ τ₁ ⇒ τ₂)
              → (bodyδ : [ θ ] Γ , τ₁ ⊢ ε ⦂ τ₂)
              → [ θ ] Γ ⊢ SLam τ₁ ε ⦂ τ₁ ⇒ τ₂
  T-App       : (δ₁ : [ θ ] Γ ⊢ ε₁ ⦂ τ₁ ⇒ τ₂)
              → (δ₂ : [ θ ] Γ ⊢ ε₂ ⦂ τ₁)
              → [ θ ] Γ ⊢ SApp ε₁ ε₂ ⦂ ([ zero ↦τ ε₂ ] τ₂)
  T-Case      : {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → {bs : CaseBranches (Mkℕₐ (suc n)) ℓ}
              → (resδ : [ θ ] Γ ⊢ τ')
              → (scrutτδ : [ θ ] Γ ⊢ ε ⦂ ⊍ cons)
              → (branches-well-typed : BranchesHaveType θ Γ cons bs τ')
              → [ θ ] Γ ⊢ SCase ε bs ⦂ τ'
  T-Con       : ∀ {ι}
              → {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → (≡-prf : τⱼ ≡ lookup cons ι)
              → (conArg : [ θ ] Γ ⊢ ε ⦂ τⱼ)
              → (adtτ : [ θ ] Γ ⊢ ⊍ cons)
              → [ θ ] Γ ⊢ SCon ι ε cons ⦂ ⊍ cons
  T-SubW      : (<: : [ θ ] Γ ⊢ τ' <: τ)
              → (εδ : [ θ ] Γ ⊢ ε ⦂ τ')
              → [ θ ] Γ ⊢ ε S<: τ ⦂ τ

record PositiveDecision (ℓ : ℕ) : Set where
  constructor MkPD
  field
    <:-ε : CExpr ℓ

record Oracle where
  inductive
  constructor MkOracle
  open R
  field
    decide : (Γ : Ctx ℓ)
           → (b : BaseType)
           → (ρ₁ ρ₂ : Refinement (suc ℓ))
           → Maybe (PositiveDecision ℓ)
    thin   : ∀ {Γ : Ctx (k + ℓ)} {Γ' : Ctx (suc k + ℓ)} {ρ₁ ρ₂ : Refinement (suc k + ℓ)}
           → (Γ⊂Γ' : k by Γ ⊂' Γ')
           → Is-just (decide Γ b ρ₁ ρ₂)
           → Is-just (decide Γ' b (R.act-ρ (ext-k' (suc k) suc) ρ₁) (act-ρ (ext-k' (suc k) suc) ρ₂))
    subst  : ∀ {Δ : ,-CtxSuffix ℓ σ k} {ρ₁ ρ₂ : Refinement (suc (suc k + ℓ))}
           -- TODO add this back when parametrizing everything by an oracle: → Γ ⊢ ε ⦂ σ
           → Is-just (decide (Γ ,σ, Δ) b ρ₁ ρ₂)
           → Is-just (decide (Γ ++ ([↦Δ ε ] Δ)) b
                        (S.act-ρ (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) ρ₁)
                        (S.act-ρ (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) ρ₂))
    trans : Is-just (decide Γ b ρ₁ ρ₂)
          → Is-just (decide Γ b ρ₂ ρ₃)
          → Is-just (decide Γ b ρ₁ ρ₃)
    narrowing
          -- TODO add this back when parametrizing everything by an oracle: → Γ ⊢ σ' <: σ
          : Is-just (decide (Γ , σ  ++ Δ) b ρ₁ ρ₂)
          → Is-just (decide (Γ , σ' ++ Δ) b ρ₁ ρ₂)

    thin-ε : ∀ {Γ : Ctx (k + ℓ)} {Γ' : Ctx (suc k + ℓ)} {ρ₁ ρ₂ : Refinement (suc k + ℓ)}
           → (is-just : Is-just (decide Γ b ρ₁ ρ₂))
           → (Γ⊂Γ' : k by Γ ⊂' Γ')
           → PositiveDecision.<:-ε (to-witness (thin Γ⊂Γ' is-just))
             ≡
             CR.act-ε (ext-k' k suc) (PositiveDecision.<:-ε (to-witness is-just))

data [_]_⊢_<:_ {ℓ} θ Γ where
  ST-Base : (oracle : Oracle)
          → Is-just (Oracle.decide oracle Γ b ρ₁ ρ₂)
          → [ θ ] Γ ⊢ ⟨ b ∣ ρ₁ ⟩ <: ⟨ b ∣ ρ₂ ⟩
  ST-Arr  : [ θ ] Γ ⊢ τ₁' <: τ₁
          → [ θ ] Γ , τ₁' ⊢ τ₂ <: τ₂'
          → [ θ ] Γ ⊢ τ₁ ⇒ τ₂
          → [ θ ] Γ ⊢ τ₁'
          → [ θ ] Γ ⊢ τ₁ ⇒ τ₂ <: τ₁' ⇒ τ₂'
