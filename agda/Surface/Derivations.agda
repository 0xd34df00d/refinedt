{-# OPTIONS --safe #-}

module Surface.Derivations where

open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Data.Maybe
open import Data.List.Membership.Propositional
open import Data.Vec
open import Data.Vec.Relation.Unary.All public

open import Surface.WellScoped
open        Surface.WellScoped.SubstScoped using ([_↦ₜ_]_)
-- TODO clean up modules
-- open import Surface.Substitutions
-- open import Misc.ContextConcat
-- open import Misc.Sublist

record PositiveDecision : Set where
  constructor MkPD

record Oracle : Set where
  constructor MkOracle
  open Surface.WellScoped.RenameScoped
  field
    decide : (Γ : Ctx ℓ) → (b : BaseType) → (ρ₁ ρ₂ : Refinement (suc ℓ)) → Maybe PositiveDecision
    thin   : ∀ {Γ : Ctx ℓ} {Γ' : Ctx ℓ'}
           → (Γ⊂Γ' : Γ ⊂ Γ')
           → Is-just (decide Γ b ρ₁ ρ₂)
           → Is-just (decide Γ' b (act-ρ (ext (_⊂_.ρ Γ⊂Γ')) ρ₁) (act-ρ (ext (_⊂_.ρ Γ⊂Γ')) ρ₂))

data _ok : (Γ : Ctx ℓ) → Set
data _⊢_⦂_ : (Γ : Ctx ℓ) → (ε : STerm ℓ) → (τ : SType ℓ) → Set
data _⊢_<:_ : (Γ : Ctx ℓ) → (τ₁ τ₂ : SType ℓ) → Set
data _⊢_ : (Γ : Ctx ℓ) → (τ : SType ℓ) → Set

infix 2 _⊢_⦂_
infix 2 _⊢_<:_
infix 1 _⊢_

data BranchesHaveType (Γ : Ctx ℓ) : (cons : ADTCons nₐ ℓ) → (bs : CaseBranches nₐ ℓ) → (τ' : SType ℓ) → Set where
  NoBranches    : BranchesHaveType Γ [] [] τ'
  OneMoreBranch : ∀ {conτ} {cons' : ADTCons nₐ ℓ} {bs' : CaseBranches nₐ ℓ}
                → (εδ : (Γ , conτ) ⊢ ε' ⦂ RenameScoped.weaken-τ τ')
                → (rest : BranchesHaveType Γ cons' bs' τ')
                → BranchesHaveType Γ (conτ ∷ cons') (MkCaseBranch ε' ∷ bs') τ'

data _ok where
  TCTX-Empty : ⊘ ok
  TCTX-Bind  : (prevOk : Γ ok)
             → (τδ : Γ ⊢ τ)
             → (Γ , τ) ok

data _⊢_ where
  TWF-TrueRef : Γ ok
              → Γ ⊢ ⟨ b ∣ Τ ⟩
  TWF-Base    : (ε₁δ : Γ , ⟨ b ∣ Τ ⟩ ⊢ ε₁ ⦂ ⟨ b' ∣ Τ ⟩)
              → (ε₂δ : Γ , ⟨ b ∣ Τ ⟩ ⊢ ε₂ ⦂ ⟨ b' ∣ Τ ⟩)
              → Γ ⊢ ⟨ b ∣ ε₁ ≈ ε₂ ⟩
  TWF-Conj    : (ρ₁δ : Γ ⊢ ⟨ b ∣ ρ₁ ⟩)
              → (ρ₂δ : Γ ⊢ ⟨ b ∣ ρ₂ ⟩)
              → Γ ⊢ ⟨ b ∣ ρ₁ ∧ ρ₂ ⟩
  TWF-Arr     : (argδ : Γ ⊢ τ₁)
              → (resδ : Γ , τ₁ ⊢ τ₂)
              → Γ ⊢ τ₁ ⇒ τ₂
  TWF-ADT     : ∀ {adtCons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → (consδs : All (Γ ⊢_) adtCons)
              → Γ ⊢ ⊍ adtCons

data _⊢_⦂_ where
  T-Unit      : (Γok : Γ ok)
              → Γ ⊢ SUnit ⦂ ⟨ BUnit ∣ Τ ⟩
  T-Var       : (Γok : Γ ok)
              → τ ∈ Γ at idx
              → Γ ⊢ SVar idx ⦂ τ
  T-Abs       : (arrδ : Γ ⊢ τ₁ ⇒ τ₂)
              → (bodyδ : Γ , τ₁ ⊢ ε ⦂ τ₂)
              → (Γ ⊢ SLam τ₁ ε ⦂ τ₁ ⇒ τ₂)
  T-App       : (δ₁ : Γ ⊢ ε₁ ⦂ τ₁ ⇒ τ₂)
              → (δ₂ : Γ ⊢ ε₂ ⦂ τ₁)
              → Γ ⊢ SApp ε₁ ε₂ ⦂ [ zero ↦ₜ ε₁ ] τ₂
  T-Case      : ∀ {cons : ADTCons (Mkℕₐ (suc n)) ℓ} {bs : CaseBranches (Mkℕₐ (suc n)) ℓ}
              → (resδ : Γ ⊢ τ')
              → (scrutτδ : Γ ⊢ ε ⦂ ⊍ cons)
              → (branches : BranchesHaveType Γ cons bs τ')
              → Γ ⊢ SCase ε bs ⦂ τ'
  T-Con       : ∀ {idx} {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → (conArg : Γ ⊢ ε ⦂ τⱼ)
              → (adtτ : Γ ⊢ ⊍ cons)
              → Γ ⊢ SCon idx ε cons ⦂ ⊍ cons
  T-Sub       : (Γ ⊢ ε ⦂ τ)
              → (Γ ⊢ τ')
              → (Γ ⊢ τ <: τ')
              → Γ ⊢ ε ⦂ τ'

data _⊢_<:_ where
  ST-Base     : (oracle : Oracle)
              → Is-just (Oracle.decide oracle Γ b ρ₁ ρ₂)
              → Γ ⊢ ⟨ b ∣ ρ₁ ⟩ <: ⟨ b ∣ ρ₂ ⟩
  ST-Arr      : Γ ⊢ τ₁' <: τ₁
              → Γ , τ₁' ⊢ τ₂ <: τ₂'
              → Γ ⊢ τ₁ ⇒ τ₂ <: τ₁' ⇒ τ₂'
