{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic where

open import Data.Fin using (zero; suc)
open import Data.Maybe
open import Data.Nat.Base using (_+_)
open import Data.Vec using (lookup; _∷_; [])
open import Data.Vec.Relation.Unary.All using (All; _∷_; []) public
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Common.Helpers

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Subcontext
open import Surface.Syntax.Substitution using ([_↦τ_]_; [_↦Γ_]_)
open import Surface.Syntax.Membership
import Surface.Syntax.Renaming as R
import Surface.Syntax.Substitution as S

open import Core.Syntax using (CExpr)
open import Core.Syntax.Renaming as CR using (act-ε)

data TSFlavour : Set where
  M E : TSFlavour

variable
  φ : TSFlavour

data Enrich (A : Set) : TSFlavour → Set where
  omitted   : Enrich A M
  enriched  : (δ : A)
            → Enrich A E

as-enrichment : ∀ {A}
              → A
              → Enrich A φ
as-enrichment {φ = M} δ = omitted
as-enrichment {φ = E} δ = enriched δ

record Oracle : Set

data _ok[_]     : (Γ : Ctx ℓ) → TSFlavour → Set
data _⊢[_]_⦂_   (Γ : Ctx ℓ) (φ : TSFlavour) : (ε : STerm ℓ) → (τ : SType ℓ) → Set
data _⊢[_]_<:_  (Γ : Ctx ℓ) (φ : TSFlavour) : (τ τ' : SType ℓ) → Set
data _⊢[_]_     (Γ : Ctx ℓ) (φ : TSFlavour) : (τ : SType ℓ) → Set

infix 2 _⊢[_]_⦂_
infix 2 _⊢[_]_<:_
infix 1 _⊢[_]_

data BranchesHaveType (φ : TSFlavour) (Γ : Ctx ℓ)
                    : (cons : ADTCons nₐ ℓ)
                    → (bs : CaseBranches nₐ ℓ)
                    → (τ' : SType ℓ)
                    → Set
                    where
  NoBranches    : BranchesHaveType φ Γ [] [] τ'
  OneMoreBranch : ∀ {conτ} {cons' : ADTCons nₐ ℓ} {bs' : CaseBranches nₐ ℓ}
                → (εδ : (Γ , conτ) ⊢[ φ ] ε' ⦂ R.weaken-τ τ')
                → (rest : BranchesHaveType φ Γ cons' bs' τ')
                → BranchesHaveType φ Γ (conτ ∷ cons') (MkCaseBranch ε' ∷ bs') τ'

data _ok[_] where
  TCTX-Empty : ⊘ ok[ φ ]
  TCTX-Bind  : (prevOk : Γ ok[ φ ])
             → (τδ : Γ ⊢[ φ ] τ)
             → (Γ , τ) ok[ φ ]

data _⊢[_]_ {ℓ} Γ φ where
  TWF-TrueRef : (Γok : Γ ok[ φ ])
              → Γ ⊢[ φ ] ⟨ b ∣ Τ ⟩
  TWF-Base    : (ε₁δ : Γ , ⟨ b ∣ Τ ⟩ ⊢[ φ ] ε₁ ⦂ ⟨ b' ∣ Τ ⟩)
              → (ε₂δ : Γ , ⟨ b ∣ Τ ⟩ ⊢[ φ ] ε₂ ⦂ ⟨ b' ∣ Τ ⟩)
              → Γ ⊢[ φ ] ⟨ b ∣ ε₁ ≈ ε₂ of ⟨ b' ∣ Τ ⟩ ⟩
  TWF-Conj    : (ρ₁δ : Γ ⊢[ φ ] ⟨ b ∣ ρ₁ ⟩)
              → (ρ₂δ : Γ ⊢[ φ ] ⟨ b ∣ ρ₂ ⟩)
              → Γ ⊢[ φ ] ⟨ b ∣ ρ₁ ∧ ρ₂ ⟩
  TWF-Arr     : (argδ : Γ ⊢[ φ ] τ₁)
              → (resδ : Γ , τ₁ ⊢[ φ ] τ₂)
              → Γ ⊢[ φ ] τ₁ ⇒ τ₂
  TWF-ADT     : {adtCons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → (consδs : All (Γ ⊢[ φ ]_) adtCons)
              → Γ ⊢[ φ ] ⊍ adtCons

data _⊢[_]_⦂_ {ℓ} Γ φ where
  T-Unit      : (Γok : Γ ok[ φ ])
              → Γ ⊢[ φ ] SUnit ⦂ ⟨ BUnit ∣ Τ ⟩
  T-Var       : (Γok : Γ ok[ φ ])
              → τ ∈ Γ at ι
              → Γ ⊢[ φ ] SVar ι ⦂ τ
  T-Abs       : (arrδ : Γ ⊢[ φ ] τ₁ ⇒ τ₂)
              → (bodyδ : Γ , τ₁ ⊢[ φ ] ε ⦂ τ₂)
              → Γ ⊢[ φ ] SLam τ₁ ε ⦂ τ₁ ⇒ τ₂
  T-App       : (δ₁ : Γ ⊢[ φ ] ε₁ ⦂ τ₁ ⇒ τ₂)
              → (δ₂ : Γ ⊢[ φ ] ε₂ ⦂ τ₁')
              → (<: : Γ ⊢[ φ ] τ₁' <: τ₁)
              → (resτ-≡ : τ ≡ [ zero ↦τ ε₂ ] τ₂)
              → (resτδ : Γ ⊢[ φ ] τ) -- TODO double-check it's really needed
              → Γ ⊢[ φ ] SApp ε₁ ε₂ ⦂ τ
  T-Case      : {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → {bs : CaseBranches (Mkℕₐ (suc n)) ℓ}
              → (resδ : Γ ⊢[ φ ] τ')
              → (scrutτδ : Γ ⊢[ φ ] ε ⦂ ⊍ cons)
              → (branches-well-typed : BranchesHaveType φ Γ cons bs τ')
              → Γ ⊢[ φ ] SCase ε bs ⦂ τ'
  T-Con       : ∀ {ι}
              → {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → (≡-prf : τⱼ ≡ lookup cons ι)
              → (conArg : Γ ⊢[ φ ] ε ⦂ τⱼ)
              → (adtτ : Γ ⊢[ φ ] ⊍ cons)
              → Γ ⊢[ φ ] SCon ι ε cons ⦂ ⊍ cons

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
                        (S.act-ρ (S.ext (S.replace-at (S.ctx-idx k) (R.weaken-ε-k k ε))) ρ₁)
                        (S.act-ρ (S.ext (S.replace-at (S.ctx-idx k) (R.weaken-ε-k k ε))) ρ₂))
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

data _⊢[_]_<:_ {ℓ} Γ φ where
  ST-Base : (oracle : Oracle)
          → Is-just (Oracle.decide oracle Γ b ρ₁ ρ₂)
          → Γ ⊢[ φ ] ⟨ b ∣ ρ₁ ⟩ <: ⟨ b ∣ ρ₂ ⟩
  ST-Arr  : Γ ⊢[ φ ] τ₁' <: τ₁
          → Γ , τ₁' ⊢[ φ ] τ₂ <: τ₂'
          → Enrich (Γ ⊢[ φ ] τ₁ ⇒ τ₂) φ
          → Enrich (Γ ⊢[ φ ] τ₁') φ
          → Γ ⊢[ φ ] τ₁ ⇒ τ₂ <: τ₁' ⇒ τ₂'

UniquenessOfOracles : Set
UniquenessOfOracles = ∀ (ω₁ ω₂ : Oracle) → ω₁ ≡ ω₂
