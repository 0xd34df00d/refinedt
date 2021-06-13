{-# OPTIONS --safe #-}

module Surface.Derivations where

open import Data.Fin using (zero)
open import Data.Maybe
open import Data.Nat.Base using (_+_)
open import Data.Vec using (lookup; _∷_; [])
open import Data.Vec.Relation.Unary.All using (All; _∷_; []) public
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Substitution using ([_↦τ_]_; [_↦Γ_]_)
open import Surface.Syntax.Membership
open import Surface.Operational.BetaEquivalence
import Surface.Syntax.Renaming as R
import Surface.Syntax.Substitution as S

open import Core.Syntax using (CExpr)

record PositiveDecision (ℓ : ℕ) : Set where
  constructor MkPD
  field
    <:-ε : CExpr ℓ

record Oracle : Set

data _ok : (Γ : Ctx ℓ) → Set
data _⊢_⦂_ : (Γ : Ctx ℓ) → (ε : STerm ℓ) → (τ : SType ℓ) → Set
data _⊢_<:_ : (Γ : Ctx ℓ) → (τ τ' : SType ℓ) → Set
data _⊢_ : (Γ : Ctx ℓ) → (τ : SType ℓ) → Set

infix 2 _⊢_⦂_
infix 2 _⊢_<:_
infix 1 _⊢_

data BranchesHaveType (Γ : Ctx ℓ) : (cons : ADTCons nₐ ℓ)
                                  → (bs : CaseBranches nₐ ℓ)
                                  → (τ' : SType ℓ)
                                  → Set
                                  where
  NoBranches    : BranchesHaveType Γ [] [] τ'
  OneMoreBranch : ∀ {conτ} {cons' : ADTCons nₐ ℓ} {bs' : CaseBranches nₐ ℓ}
                → (εδ : (Γ , conτ) ⊢ ε' ⦂ R.weaken-τ τ')
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
              → Γ ⊢ ⟨ b ∣ ε₁ ≈ ε₂ of ⟨ b' ∣ Τ ⟩ ⟩
  TWF-Conj    : (ρ₁δ : Γ ⊢ ⟨ b ∣ ρ₁ ⟩)
              → (ρ₂δ : Γ ⊢ ⟨ b ∣ ρ₂ ⟩)
              → Γ ⊢ ⟨ b ∣ ρ₁ ∧ ρ₂ ⟩
  TWF-Arr     : (argδ : Γ ⊢ τ₁)
              → (resδ : Γ , τ₁ ⊢ τ₂)
              → Γ ⊢ τ₁ ⇒ τ₂
  TWF-ADT     : {adtCons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → (consδs : All (Γ ⊢_) adtCons)
              → Γ ⊢ ⊍ adtCons

data _⊢_⦂_ where
  T-Unit      : (Γok : Γ ok)
              → Γ ⊢ SUnit ⦂ ⟨ BUnit ∣ Τ ⟩
  T-Var       : (Γok : Γ ok)
              → τ ∈ Γ at ι
              → Γ ⊢ SVar ι ⦂ τ
  T-Abs       : (arrδ : Γ ⊢ τ₁ ⇒ τ₂)
              → (bodyδ : Γ , τ₁ ⊢ ε ⦂ τ₂)
              → Γ ⊢ SLam τ₁ ε ⦂ τ₁ ⇒ τ₂
  T-App       : (δ₁ : Γ ⊢ ε₁ ⦂ τ₁ ⇒ τ₂)
              → (δ₂ : Γ ⊢ ε₂ ⦂ τ₁)
              → Γ ⊢ SApp ε₁ ε₂ ⦂ [ zero ↦τ ε₂ ] τ₂
  T-Case      : {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → {bs : CaseBranches (Mkℕₐ (suc n)) ℓ}
              → (resδ : Γ ⊢ τ')
              → (scrutτδ : Γ ⊢ ε ⦂ ⊍ cons)
              → (branches-well-typed : BranchesHaveType Γ cons bs τ')
              → Γ ⊢ SCase ε bs ⦂ τ'
  T-Con       : ∀ {ι}
              → {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → (≡-prf : τⱼ ≡ lookup cons ι)
              → (conArg : Γ ⊢ ε ⦂ τⱼ)
              → (adtτ : Γ ⊢ ⊍ cons)
              → Γ ⊢ SCon ι ε cons ⦂ ⊍ cons
  T-Sub       : (εδ : Γ ⊢ ε ⦂ τ)
              → (τ'δ : Γ ⊢ τ')
              → (<: : Γ ⊢ τ <: τ')
              → Γ ⊢ ε ⦂ τ'
  T-RConv     : (εδ : Γ ⊢ ε ⦂ τ)
              → (τ'δ : Γ ⊢ τ')
              → (τ~τ' : τ ↭βτ τ')
              → Γ ⊢ ε ⦂ τ'

record Oracle where
  inductive
  constructor MkOracle
  open R
  field
    decide : (Γ : Ctx ℓ)
           → (b : BaseType)
           → (ρ₁ ρ₂ : Refinement (suc ℓ))
           → Maybe (PositiveDecision ℓ)
    thin   : ∀ {Γ : Ctx ℓ} {Γ' : Ctx ℓ'}
           → (Γ⊂Γ' : Γ ⊂ Γ')
           → Is-just (decide Γ b ρ₁ ρ₂)
           → Is-just (decide Γ' b (act-ρ (ext (_⊂_.ρ Γ⊂Γ')) ρ₁) (act-ρ (ext (_⊂_.ρ Γ⊂Γ')) ρ₂))
    subst  : ∀ {Δ : ,-CtxSuffix ℓ σ k} {ρ₁ ρ₂ : Refinement (suc (suc k + ℓ))}
           -- TODO add this back when parametrizing everything by an oracle: → Γ ⊢ ε ⦂ σ
           → Is-just (decide (Γ ,σ, Δ) b ρ₁ ρ₂)
           → Is-just (decide (Γ ++ ([↦Δ ε ] Δ)) b
                        (S.act-ρ (S.ext (S.replace-at (S.ctx-idx k) (R.weaken-ε-k k ε))) ρ₁)
                        (S.act-ρ (S.ext (S.replace-at (S.ctx-idx k) (R.weaken-ε-k k ε))) ρ₂))
    trans : Is-just (decide Γ b ρ₁ ρ₂)
          → Is-just (decide Γ b ρ₂ ρ₃)
          → Is-just (decide Γ b ρ₁ ρ₃)
    narrowing
          -- TODO add this back when parametrizing everything by an oracle: → Γ ⊢ σ' <: σ
          : Is-just (decide (Γ , σ  ++ Δ) b ρ₁ ρ₂)
          → Is-just (decide (Γ , σ' ++ Δ) b ρ₁ ρ₂)
    stepping
          : τ ↭βτ τ'
          → Is-just (decide (Γ , τ  ++ Δ) b ρ₁ ρ₂)
          → Is-just (decide (Γ , τ' ++ Δ) b ρ₁ ρ₂)


-- Purely technical requirement to avoid parametrizing all of the modules by the same oracle and making hole types ugly
record UniquenessOfOracles : Set where
  field
    oracles-equal : ∀ (ω₁ ω₂ : Oracle) → ω₁ ≡ ω₂

data _⊢_<:_ where
  ST-Base     : (oracle : Oracle)
              → ⦃ UoO : UniquenessOfOracles ⦄
              → Is-just (Oracle.decide oracle Γ b ρ₁ ρ₂)
              → Γ ⊢ ⟨ b ∣ ρ₁ ⟩ <: ⟨ b ∣ ρ₂ ⟩
  ST-Arr      : Γ ⊢ τ₁' <: τ₁
              → Γ , τ₁' ⊢ τ₂ <: τ₂'
              → Γ ⊢ τ₁ ⇒ τ₂ <: τ₁' ⇒ τ₂'
