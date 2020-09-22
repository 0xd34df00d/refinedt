module Surface.Derivations where

open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Data.Maybe
open import Data.List.Membership.Propositional
open import Data.Vec
open import Data.Vec.Relation.Unary.All public

open import Surface.Syntax
open import Surface.Substitutions
open import Misc.ContextConcat
open import Sublist

record PositiveDecision : Set where
  constructor MkPD

record Oracle : Set where
  constructor MkOracle
  field
    decide : (Γ : Ctx) → (var : Var) → (b : BaseType) → (ρ₁ ρ₂ : Refinement) → Maybe PositiveDecision
    thin   : ∀ {var b ρ₁ ρ₂}
           → Γ ⊂ Γ'
           → Is-just (decide Γ var b ρ₁ ρ₂)
           → Is-just (decide Γ' var b ρ₁ ρ₂)
    exchange : ∀ {var b ρ₁ ρ₂}
             → Is-just (decide (Γ , x₁ ⦂ τ₁ , x₂ ⦂ τ₂ , Δ) var b ρ₁ ρ₂)
             → Is-just (decide (Γ , x₂ ⦂ τ₂ , x₁ ⦂ τ₁ , Δ) var b ρ₁ ρ₂)

data _ok : (Γ : Ctx) → Set
data _⊢_⦂_ : (Γ : Ctx) → (ε : STerm) → (τ : SType) → Set
data _⊢_<:_ : (Γ : Ctx) → (τ₁ τ₂ : SType) → Set
data _⊢_ : (Γ : Ctx) → (τ : SType) → Set

infix 19 _⊢_

data BranchesHaveType : ∀ {n} (Γ : Ctx) → (cons : ADTCons n) → (bs : CaseBranches n) → (τ' : SType) → Set where
  NoBranches    : BranchesHaveType Γ [] [] τ'
  OneMoreBranch : ∀ {conτ} {cons' : ADTCons n} {bs' : CaseBranches n}
                → (εδ : (Γ , x ⦂ conτ) ⊢ ε' ⦂ τ')
                → (rest : BranchesHaveType Γ cons' bs' τ')
                → BranchesHaveType Γ (conτ ∷ cons') (MkCaseBranch x ε' ∷ bs') τ'

data _ok where
  TCTX-Empty : [] ok
  TCTX-Bind  : (prevOk : Γ ok)
             → (τδ : Γ ⊢ τ)
             → (Γ , ν ⦂ τ) ok

data _⊢_ where
  TWF-TrueRef : Γ ok
              → Γ ⊢ (ν ∈ b ∣ Τ)
  TWF-Base    : (ε₁δ : (Γ , ν ⦂ (ν₁ ∈ b ∣ Τ)) ⊢ ε₁ ⦂ (ν₂ ∈ b' ∣ Τ))
              → (ε₂δ : (Γ , ν ⦂ (ν₁ ∈ b ∣ Τ)) ⊢ ε₂ ⦂ (ν₂ ∈ b' ∣ Τ))
              → Γ ⊢ (ν ∈ b ∣ ε₁ ≈ ε₂)
  TWF-Conj    : (ρ₁δ : Γ ⊢ (ν ∈ b ∣ ρ₁))
              → (ρ₂δ : Γ ⊢ (ν ∈ b ∣ ρ₂))
              → Γ ⊢ (ν ∈ b ∣ ρ₁ ∧ ρ₂)
  TWF-Arr     : (argδ : Γ ⊢ τ₁)
              → (resδ : (Γ , x ⦂ τ₁) ⊢ τ₂)
              → Γ ⊢ SArr x τ₁ τ₂
  TWF-ADT     : ∀ {adtCons : ADTCons (suc n)}
              → (consδs : All (Γ ⊢_) adtCons)
              → Γ ⊢ SADT adtCons

data _⊢_⦂_ where
  T-Unit      : (gok : Γ ok)
              → Γ ⊢ SUnit ⦂ (ν ∈ BUnit ∣ Τ)
  T-Var       : (gok : Γ ok)
              → x ⦂ τ ∈ Γ
              → Γ ⊢ SVar x ⦂ τ
  T-Abs       : (arrδ : Γ ⊢ SArr x τ₁ τ₂)
              → (bodyδ : (Γ , x ⦂ τ₁) ⊢ ε ⦂ τ₂)
              → (Γ ⊢ SLam x τ₁ ε ⦂ SArr x τ₁ τ₂)
  T-App       : (δ₁ : Γ ⊢ ε₁ ⦂ SArr x τ₁ τ₂)
              → (δ₂ : Γ ⊢ ε₂ ⦂ τ₁)
              → Γ ⊢ SApp ε₁ ε₂ ⦂ [ x ↦ₜ ε₂ ] τ₂
  T-Case      : ∀ {cons : ADTCons (suc n)} {bs : CaseBranches (suc n)}
              → (resδ : Γ ⊢ τ')
              → (scrutτδ : Γ ⊢ ε ⦂ SADT cons)
              → (branches : BranchesHaveType Γ cons bs τ')
              → Γ ⊢ SCase ε bs ⦂ τ'
  T-Con       : ∀ {idx} {cons : ADTCons (suc n)}
              → (conArg : Γ ⊢ ε ⦂ τⱼ)
              → (adtτ : Γ ⊢ SADT cons)
              → Γ ⊢ SCon idx ε cons ⦂ SADT cons
  T-Sub       : (Γ ⊢ ε ⦂ τ)
              → (Γ ⊢ τ')
              → (Γ ⊢ τ <: τ')
              → Γ ⊢ ε ⦂ τ'

data _⊢_<:_ where
  ST-Base     : (oracle : Oracle)
              → Is-just (Oracle.decide oracle Γ ν b ρ₁ ρ₂)
              → Γ ⊢ (ν ∈ b ∣ ρ₁) <: (ν ∈ b ∣ ρ₂)
  ST-Arr      : Γ ⊢ τ₁' <: τ₁
              → (Γ , x ⦂ τ₁') ⊢ τ₂ <: τ₂'
              → Γ ⊢ SArr x τ₁ τ₂ <: SArr x τ₁' τ₂'
