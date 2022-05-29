{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic where

open import Data.Fin using (zero; suc)
open import Data.Maybe using (Is-just)
open import Data.Nat.Base using (_+_)
open import Data.Vec using (lookup; _∷_; [])
open import Data.Vec.Relation.Unary.All using (All; _∷_; []) public
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Common.Helpers

open import Surface.Syntax
open import Surface.Syntax.Membership
open import Surface.Syntax.Substitution using ([_↦τ_]_)
import Surface.Syntax.Renaming as R
open import Surface.Oracle public
open import Surface.Derivations.Common public

data RuleKind : Set where
  t-sub not-t-sub : RuleKind

variable
  κ κ' κ₁ κ₂ : RuleKind
  θ : Oracle

data _ok[_,_]        : (Γ : Ctx ℓ) → Oracle → TSFlavour → Set
data _⊢[_,_of_]_⦂_   (Γ : Ctx ℓ) (θ : Oracle) (φ : TSFlavour) : (κ : RuleKind) → (ε : STerm ℓ) → (τ : SType ℓ) → Set
data _⊢[_,_]_<:_     (Γ : Ctx ℓ) (θ : Oracle) (φ : TSFlavour) : (τ τ' : SType ℓ) → Set
data _⊢[_,_]_        (Γ : Ctx ℓ) (θ : Oracle) (φ : TSFlavour) : (τ : SType ℓ) → Set

infix 2 _⊢[_,_of_]_⦂_
infix 2 _⊢[_,_]_<:_
infix 1 _⊢[_,_]_

data BranchesHaveType (θ : Oracle) (φ : TSFlavour) (Γ : Ctx ℓ)
                    : (cons : ADTCons nₐ ℓ)
                    → (bs : CaseBranches nₐ ℓ)
                    → (τ' : SType ℓ)
                    → Set
                    where
  NoBranches    : BranchesHaveType θ φ Γ [] [] τ'
  OneMoreBranch : ∀ {conτ} {cons' : ADTCons nₐ ℓ} {bs' : CaseBranches nₐ ℓ}
                → (εδ : (Γ , conτ) ⊢[ θ , φ of not-t-sub ] ε' ⦂ R.weaken-τ τ')
                → (rest : BranchesHaveType θ φ Γ cons' bs' τ')
                → BranchesHaveType θ φ Γ (conτ ∷ cons') (MkCaseBranch ε' ∷ bs') τ'

data _ok[_,_] where
  TCTX-Empty : ⊘ ok[ θ , φ ]
  TCTX-Bind  : (prevOk : Γ ok[ θ , φ ])
             → (τδ : Γ ⊢[ θ , φ ] τ)
             → (Γ , τ) ok[ θ , φ ]

data _⊢[_,_]_ {ℓ} Γ θ φ where
  TWF-TrueRef : (Γok : Γ ok[ θ , φ ])
              → Γ ⊢[ θ , φ ] ⟨ b ∣ Τ ⟩
  TWF-Base    : (ε₁δ : Γ , ⟨ b ∣ Τ ⟩ ⊢[ θ , φ of not-t-sub ] ε₁ ⦂ ⟨ b' ∣ Τ ⟩)
              → (ε₂δ : Γ , ⟨ b ∣ Τ ⟩ ⊢[ θ , φ of not-t-sub ] ε₂ ⦂ ⟨ b' ∣ Τ ⟩)
              → Γ ⊢[ θ , φ ] ⟨ b ∣ ε₁ ≈ ε₂ of ⟨ b' ∣ Τ ⟩ ⟩
  TWF-Conj    : (ρ₁δ : Γ ⊢[ θ , φ ] ⟨ b ∣ ρ₁ ⟩)
              → (ρ₂δ : Γ ⊢[ θ , φ ] ⟨ b ∣ ρ₂ ⟩)
              → Γ ⊢[ θ , φ ] ⟨ b ∣ ρ₁ ∧ ρ₂ ⟩
  TWF-Arr     : (argδ : Γ ⊢[ θ , φ ] τ₁)
              → (resδ : Γ , τ₁ ⊢[ θ , φ ] τ₂)
              → Γ ⊢[ θ , φ ] τ₁ ⇒ τ₂
  TWF-ADT     : {adtCons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → (consδs : All (Γ ⊢[ θ , φ ]_) adtCons)
              → Γ ⊢[ θ , φ ] ⊍ adtCons

data _⊢[_,_of_]_⦂_ {ℓ} Γ θ φ where
  T-Unit      : (Γok : Γ ok[ θ , φ ])
              → Γ ⊢[ θ , φ of not-t-sub ] SUnit ⦂ ⟨ BUnit ∣ Τ ⟩
  T-Var       : (Γok : Γ ok[ θ , φ ])
              → τ ∈ Γ at ι
              → Γ ⊢[ θ , φ of not-t-sub ] SVar ι ⦂ τ
  T-Abs       : (arrδ : Γ ⊢[ θ , φ ] τ₁ ⇒ τ₂)
              → (bodyδ : Γ , τ₁ ⊢[ θ , φ of not-t-sub ] ε ⦂ τ₂)
              → Γ ⊢[ θ , φ of not-t-sub ] SLam τ₁ ε ⦂ τ₁ ⇒ τ₂
  T-App       : (δ₁ : Γ ⊢[ θ , φ of not-t-sub ] ε₁ ⦂ τ₁ ⇒ τ₂)
              → (δ₂ : Γ ⊢[ θ , φ of t-sub ] ε₂ ⦂ τ₁)
              → (resτ-≡ : τ ≡ [ zero ↦τ ε₂ ] τ₂)
              → (resτδ : Γ ⊢[ θ , φ ] τ) -- TODO double-check it's really needed
              → Γ ⊢[ θ , φ of not-t-sub ] SApp ε₁ ε₂ ⦂ τ
  T-Case      : {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → {bs : CaseBranches (Mkℕₐ (suc n)) ℓ}
              → (resδ : Γ ⊢[ θ , φ ] τ')
              → (scrutτδ : Γ ⊢[ θ , φ of not-t-sub ] ε ⦂ ⊍ cons)
              → (branches-well-typed : BranchesHaveType θ φ Γ cons bs τ')
              → Γ ⊢[ θ , φ of not-t-sub ] SCase ε bs ⦂ τ'
  T-Con       : ∀ {ι}
              → {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → (≡-prf : τⱼ ≡ lookup cons ι)
              → (conArg : Γ ⊢[ θ , φ of not-t-sub ] ε ⦂ τⱼ)
              → (adtτ : Γ ⊢[ θ , φ ] ⊍ cons)
              → Γ ⊢[ θ , φ of not-t-sub ] SCon ι ε cons ⦂ ⊍ cons
  T-Sub       : (εδ : Γ ⊢[ θ , φ of not-t-sub ] ε ⦂ τ)
              → (τ'δ : Γ ⊢[ θ , φ ] τ')
              → (<: : Γ ⊢[ θ , φ ] τ <: τ')
              → Γ ⊢[ θ , φ of t-sub ] ε ⦂ τ'

data _⊢[_,_]_<:_ {ℓ} Γ θ φ where
  ST-Base : Is-just (Oracle.decide θ Γ b ρ₁ ρ₂)
          → Γ ⊢[ θ , φ ] ⟨ b ∣ ρ₁ ⟩ <: ⟨ b ∣ ρ₂ ⟩
  ST-Arr  : Γ ⊢[ θ , φ ] τ₁' <: τ₁
          → Γ , τ₁' ⊢[ θ , φ ] τ₂ <: τ₂'
          → Enrich (Γ ⊢[ θ , φ ] τ₁ ⇒ τ₂) φ
          → Enrich (Γ ⊢[ θ , φ ] τ₁') φ
          → Γ ⊢[ θ , φ ] τ₁ ⇒ τ₂ <: τ₁' ⇒ τ₂'
