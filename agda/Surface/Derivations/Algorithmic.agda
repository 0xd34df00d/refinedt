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
open import Surface.Oracle
open import Surface.Derivations.Common public

data RuleKind : Set where
  t-sub not-t-sub : RuleKind

variable
  κ κ' κ₁ κ₂ : RuleKind
  θ : Oracle

data _ok[_]        : (Γ : Ctx ℓ) → TSFlavour → Set
data _⊢[_of_]_⦂_   (Γ : Ctx ℓ) (φ : TSFlavour) : (κ : RuleKind) → (ε : STerm ℓ) → (τ : SType ℓ) → Set
data _⊢[_]_<:_     (Γ : Ctx ℓ) (φ : TSFlavour) : (τ τ' : SType ℓ) → Set
data _⊢[_]_        (Γ : Ctx ℓ) (φ : TSFlavour) : (τ : SType ℓ) → Set

infix 2 _⊢[_of_]_⦂_
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
                → (εδ : (Γ , conτ) ⊢[ φ of not-t-sub ] ε' ⦂ R.weaken-τ τ')
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
  TWF-Base    : (ε₁δ : Γ , ⟨ b ∣ Τ ⟩ ⊢[ φ of not-t-sub ] ε₁ ⦂ ⟨ b' ∣ Τ ⟩)
              → (ε₂δ : Γ , ⟨ b ∣ Τ ⟩ ⊢[ φ of not-t-sub ] ε₂ ⦂ ⟨ b' ∣ Τ ⟩)
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

data _⊢[_of_]_⦂_ {ℓ} Γ φ where
  T-Unit      : (Γok : Γ ok[ φ ])
              → Γ ⊢[ φ of not-t-sub ] SUnit ⦂ ⟨ BUnit ∣ Τ ⟩
  T-Var       : (Γok : Γ ok[ φ ])
              → τ ∈ Γ at ι
              → Γ ⊢[ φ of not-t-sub ] SVar ι ⦂ τ
  T-Abs       : (arrδ : Γ ⊢[ φ ] τ₁ ⇒ τ₂)
              → (bodyδ : Γ , τ₁ ⊢[ φ of not-t-sub ] ε ⦂ τ₂)
              → Γ ⊢[ φ of not-t-sub ] SLam τ₁ ε ⦂ τ₁ ⇒ τ₂
  T-App       : (δ₁ : Γ ⊢[ φ of not-t-sub ] ε₁ ⦂ τ₁ ⇒ τ₂)
              → (δ₂ : Γ ⊢[ φ of t-sub ] ε₂ ⦂ τ₁)
              → (resτ-≡ : τ ≡ [ zero ↦τ ε₂ ] τ₂)
              → (resτδ : Γ ⊢[ φ ] τ) -- TODO double-check it's really needed
              → Γ ⊢[ φ of not-t-sub ] SApp ε₁ ε₂ ⦂ τ
  T-Case      : {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → {bs : CaseBranches (Mkℕₐ (suc n)) ℓ}
              → (resδ : Γ ⊢[ φ ] τ')
              → (scrutτδ : Γ ⊢[ φ of not-t-sub ] ε ⦂ ⊍ cons)
              → (branches-well-typed : BranchesHaveType φ Γ cons bs τ')
              → Γ ⊢[ φ of not-t-sub ] SCase ε bs ⦂ τ'
  T-Con       : ∀ {ι}
              → {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
              → (≡-prf : τⱼ ≡ lookup cons ι)
              → (conArg : Γ ⊢[ φ of not-t-sub ] ε ⦂ τⱼ)
              → (adtτ : Γ ⊢[ φ ] ⊍ cons)
              → Γ ⊢[ φ of not-t-sub ] SCon ι ε cons ⦂ ⊍ cons
  T-Sub       : (εδ : Γ ⊢[ φ of not-t-sub ] ε ⦂ τ)
              → (τ'δ : Γ ⊢[ φ ] τ')
              → (<: : Γ ⊢[ φ ] τ <: τ')
              → Γ ⊢[ φ of t-sub ] ε ⦂ τ'

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
