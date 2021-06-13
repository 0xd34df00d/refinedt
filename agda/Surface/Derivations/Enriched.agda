{-# OPTIONS --safe #-}
module Surface.Derivations.Enriched where

open import Data.Fin using (zero)
open import Data.Maybe using (Is-just)
open import Data.Vec using (lookup; _∷_; [])
open import Data.Vec.Relation.Unary.All using (All; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Surface.Syntax
open import Surface.Syntax.Membership
open import Surface.Syntax.Substitution using ([_↦τ_]_; [_↦Γ_]_)
import      Surface.Syntax.Renaming as R
open import Surface.Derivations using (Oracle; UniquenessOfOracles)
open import Surface.Operational.BetaEquivalence

mutual
  infix 2 _⊢ₑ_⦂_
  infix 2 _⊢ₑ_<:_
  infix 1 _⊢ₑ_

  data BranchesHaveTypeₑ (Γ : Ctx ℓ) : (cons : ADTCons nₐ ℓ)
                                     → (bs : CaseBranches nₐ ℓ)
                                     → (τ' : SType ℓ)
                                     → Set
                                     where
    NoBranches    : BranchesHaveTypeₑ Γ [] [] τ'
    OneMoreBranch : ∀ {conτ} {cons' : ADTCons nₐ ℓ} {bs' : CaseBranches nₐ ℓ}
                  → (εδ : (Γ , conτ) ⊢ₑ ε' ⦂ R.weaken-τ τ')
                  → (rest : BranchesHaveTypeₑ Γ cons' bs' τ')
                  → BranchesHaveTypeₑ Γ (conτ ∷ cons') (MkCaseBranch ε' ∷ bs') τ'

  data _okₑ : (Γ : Ctx ℓ) → Set where
    TCTX-Empty : ⊘ okₑ
    TCTX-Bind  : (prevOk : Γ okₑ)
               → (τδ : Γ ⊢ₑ τ)
               → (Γ , τ) okₑ

  data _⊢ₑ_ : (Γ : Ctx ℓ) → (τ : SType ℓ) → Set where
    TWF-TrueRef : Γ okₑ
                → Γ ⊢ₑ ⟨ b ∣ Τ ⟩
    TWF-Base    : (ε₁δ : Γ , ⟨ b ∣ Τ ⟩ ⊢ₑ ε₁ ⦂ ⟨ b' ∣ Τ ⟩)
                → (ε₂δ : Γ , ⟨ b ∣ Τ ⟩ ⊢ₑ ε₂ ⦂ ⟨ b' ∣ Τ ⟩)
        {- ₑ -} → Γ , ⟨ b ∣ Τ ⟩ ⊢ₑ ⟨ b' ∣ Τ ⟩
        {- ₑ -} → (Γ , ⟨ b ∣ Τ ⟩) okₑ
                → Γ ⊢ₑ ⟨ b ∣ ε₁ ≈ ε₂ of ⟨ b' ∣ Τ ⟩ ⟩
    TWF-Conj    : (ρ₁δ : Γ ⊢ₑ ⟨ b ∣ ρ₁ ⟩)
                → (ρ₂δ : Γ ⊢ₑ ⟨ b ∣ ρ₂ ⟩)
        {- ₑ -} → Γ okₑ
                → Γ ⊢ₑ ⟨ b ∣ ρ₁ ∧ ρ₂ ⟩
    TWF-Arr     : (argδ : Γ ⊢ₑ τ₁)
                → (resδ : Γ , τ₁ ⊢ₑ τ₂)
        {- ₑ -} → Γ okₑ
                → Γ ⊢ₑ τ₁ ⇒ τ₂
    TWF-ADT     : {adtCons : ADTCons (Mkℕₐ (suc n)) ℓ}
                → (consδs : All (Γ ⊢ₑ_) adtCons)
        {- ₑ -} → Γ okₑ
                → Γ ⊢ₑ ⊍ adtCons

  data _⊢ₑ_⦂_ : (Γ : Ctx ℓ) → (ε : STerm ℓ) → (τ : SType ℓ) → Set where
    T-Unit      : (Γok : Γ okₑ)
        {- ₑ -} → Γ ⊢ₑ ⟨ BUnit ∣ Τ ⟩
                → Γ ⊢ₑ SUnit ⦂ ⟨ BUnit ∣ Τ ⟩
    T-Var       : (Γok : Γ okₑ)
                → τ ∈ Γ at ι
        {- ₑ -} → Γ ⊢ₑ τ
                → Γ ⊢ₑ SVar ι ⦂ τ
    T-Abs       : (arrδ : Γ ⊢ₑ τ₁ ⇒ τ₂)
                → (bodyδ : Γ , τ₁ ⊢ₑ ε ⦂ τ₂)
        {- ₑ -} → Γ okₑ
        {- ₑ -} → Γ , τ₁ ⊢ₑ τ₂
                → Γ ⊢ₑ SLam τ₁ ε ⦂ τ₁ ⇒ τ₂
    T-App       : (δ₁ : Γ ⊢ₑ ε₁ ⦂ τ₁ ⇒ τ₂)
                → (δ₂ : Γ ⊢ₑ ε₂ ⦂ τ₁)
        {- ₑ -} → Γ okₑ
        {- ₑ -} → Γ ⊢ₑ τ₁ ⇒ τ₂
        {- ₑ -} → Γ ⊢ₑ [ zero ↦τ ε₂ ] τ₂
                → Γ ⊢ₑ SApp ε₁ ε₂ ⦂ [ zero ↦τ ε₂ ] τ₂
    T-Case      : {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
                → {bs : CaseBranches (Mkℕₐ (suc n)) ℓ}
                → (resδ : Γ ⊢ₑ τ')
                → (scrutτδ : Γ ⊢ₑ ε ⦂ ⊍ cons)
                → (branches-well-typed : BranchesHaveTypeₑ Γ cons bs τ')
        {- ₑ -} → Γ okₑ
                → Γ ⊢ₑ SCase ε bs ⦂ τ'
    T-Con       : ∀ {ι}
                → {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
                → (≡-prf : τⱼ ≡ lookup cons ι)
                → (conArg : Γ ⊢ₑ ε ⦂ τⱼ)
                → (adtτ : Γ ⊢ₑ ⊍ cons)
        {- ₑ -} → Γ okₑ
                → Γ ⊢ₑ SCon ι ε cons ⦂ ⊍ cons
    T-Sub       : (εδ : Γ ⊢ₑ ε ⦂ τ)
                → (τ'δ : Γ ⊢ₑ τ')
                → (<: : Γ ⊢ₑ τ <: τ')
        {- ₑ -} → (τδ : Γ ⊢ₑ τ)
                → Γ ⊢ₑ ε ⦂ τ'
    T-RConv     : (εδ : Γ ⊢ₑ ε ⦂ τ)
                → (τ'δ : Γ ⊢ₑ τ')
                → (τ~τ' : τ ↭βτ τ')
        {- ₑ -} → (τδ : Γ ⊢ₑ τ)
                → Γ ⊢ₑ ε ⦂ τ'

  data _⊢ₑ_<:_ : (Γ : Ctx ℓ) → (τ τ' : SType ℓ) → Set where
    ST-Base     : (oracle : Oracle)
                → ⦃ UoO : UniquenessOfOracles ⦄
                → Is-just (Oracle.decide oracle Γ b ρ₁ ρ₂)
        {- ₑ -} → Γ ⊢ₑ ⟨ b ∣ ρ₁ ⟩
        {- ₑ -} → Γ ⊢ₑ ⟨ b ∣ ρ₂ ⟩
                → Γ ⊢ₑ ⟨ b ∣ ρ₁ ⟩ <: ⟨ b ∣ ρ₂ ⟩
    ST-Arr      : Γ ⊢ₑ τ₁' <: τ₁
                → Γ , τ₁' ⊢ₑ τ₂ <: τ₂'
        {- ₑ -} → Γ ⊢ₑ τ₁ ⇒ τ₂
        {- ₑ -} → Γ ⊢ₑ τ₁' ⇒ τ₂'
                → Γ ⊢ₑ τ₁ ⇒ τ₂ <: τ₁' ⇒ τ₂'
