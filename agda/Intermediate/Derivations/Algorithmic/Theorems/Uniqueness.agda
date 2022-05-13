{-# OPTIONS --safe #-}

module Intermediate.Derivations.Algorithmic.Theorems.Uniqueness where

open import Data.Maybe.Relation.Unary.Any using (irrelevant)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (Irrelevant)

open import Intermediate.Syntax
open import Intermediate.Syntax.Injectivity
open import Intermediate.Syntax.Membership
open import Intermediate.Syntax.Renaming.Injectivity
open import Intermediate.Derivations.Algorithmic

∈-uniqueness : τ₁ ∈ Γ at ι
             → τ₂ ∈ Γ at ι
             → τ₁ ≡ τ₂
∈-uniqueness (∈-zero refl) (∈-zero ≡-prf) = sym ≡-prf
∈-uniqueness (∈-suc refl ∈₁) (∈-suc ≡-prf ∈₂) rewrite ∈-uniqueness ∈₁ ∈₂ = sym ≡-prf

typing-uniqueness : [ θ ] Γ ⊢ ε ⦂ τ₁
                  → [ θ ] Γ ⊢ ε ⦂ τ₂
                  → τ₁ ≡ τ₂
typing-uniqueness (T-Unit _) (T-Unit _) = refl
typing-uniqueness (T-Var _ ∈₁) (T-Var _ ∈₂) = ∈-uniqueness ∈₁ ∈₂
typing-uniqueness (T-Abs _ δ₁) (T-Abs _ δ₂) rewrite typing-uniqueness δ₁ δ₂ = refl
typing-uniqueness (T-App δ₁ _ refl _) (T-App δ₂ _ refl _) rewrite ⇒-inj₂ (typing-uniqueness δ₁ δ₂) = refl
typing-uniqueness (T-Case resδ δ₁ (OneMoreBranch εδ₁ _)) (T-Case resδ₁ δ₂ (OneMoreBranch εδ₂ _)) with typing-uniqueness δ₁ δ₂
... | refl = weaken-τ-injective (typing-uniqueness εδ₁ εδ₂)
typing-uniqueness (T-Con _ _ _) (T-Con _ _ _) = refl
typing-uniqueness (T-SubW _ _) (T-SubW _ _) = refl


unique-∈ : Irrelevant (τ ∈ Γ at ι)
unique-∈ (∈-zero refl) (∈-zero refl) = refl
unique-∈ (∈-suc {τ = τ₁} refl ∈₁) (∈-suc {τ = τ₂} ≡-prf ∈₂) with weaken-τ-injective ≡-prf | ≡-prf
... | refl | refl rewrite unique-∈ ∈₁ ∈₂ = refl

mutual
  unique-Γok : Irrelevant ([ θ ] Γ ok)
  unique-Γok TCTX-Empty TCTX-Empty = refl
  unique-Γok (TCTX-Bind δ₁ τδ₁) (TCTX-Bind δ₂ τδ₂)
    rewrite unique-Γok δ₁ δ₂
          | unique-Γ⊢τ τδ₁ τδ₂
          = refl

  unique-Γ⊢τ : Irrelevant ([ θ ] Γ ⊢ τ)
  unique-Γ⊢τ (TWF-TrueRef Γok₁) (TWF-TrueRef Γok₂)
    rewrite unique-Γok Γok₁ Γok₂
          = refl
  unique-Γ⊢τ (TWF-Base ε₁δ₁ ε₂δ₁) (TWF-Base ε₁δ₂ ε₂δ₂)
    rewrite unique-Γ⊢ε⦂τ ε₁δ₁ ε₁δ₂
          | unique-Γ⊢ε⦂τ ε₂δ₁ ε₂δ₂
          = refl
  unique-Γ⊢τ (TWF-Conj δ₁₁ δ₂₁) (TWF-Conj δ₁₂ δ₂₂)
    rewrite unique-Γ⊢τ δ₁₁ δ₁₂
          | unique-Γ⊢τ δ₂₁ δ₂₂
          = refl
  unique-Γ⊢τ (TWF-Arr δ₁₁ δ₂₁) (TWF-Arr δ₁₂ δ₂₂)
    rewrite unique-Γ⊢τ δ₁₁ δ₁₂
          | unique-Γ⊢τ δ₂₁ δ₂₂
          = refl
  unique-Γ⊢τ (TWF-ADT consδs₁) (TWF-ADT consδs₂)
    rewrite unique-cons consδs₁ consδs₂
          = refl

  unique-Γ⊢ε⦂τ : Irrelevant ([ θ ] Γ ⊢ ε ⦂ τ)
  unique-Γ⊢ε⦂τ (T-Unit Γok₁) (T-Unit Γok₂)
    rewrite unique-Γok Γok₁ Γok₂
          = refl
  unique-Γ⊢ε⦂τ (T-Var Γok₁ ∈₁) (T-Var Γok₂ ∈₂)
    rewrite unique-Γok Γok₁ Γok₂
          | unique-∈ ∈₁ ∈₂
          = refl
  unique-Γ⊢ε⦂τ (T-Abs arrδ₁ δ₁) (T-Abs arrδ₂ δ₂)
    rewrite unique-Γ⊢τ arrδ₁ arrδ₂
          | unique-Γ⊢ε⦂τ δ₁ δ₂
          = refl
  unique-Γ⊢ε⦂τ (T-App δ₁₁ δ₂₁ refl resτδ₁) (T-App δ₁₂ δ₂₂ resτ-≡₂ resτδ₂) with typing-uniqueness δ₁₁ δ₁₂
                                                                             | typing-uniqueness δ₂₁ δ₂₂
                                                                             | resτ-≡₂
  ... | refl | refl | refl
    rewrite unique-Γ⊢ε⦂τ δ₁₁ δ₁₂
          | unique-Γ⊢ε⦂τ δ₂₁ δ₂₂
          | unique-Γ⊢τ resτδ₁ resτδ₂
          = refl
  unique-Γ⊢ε⦂τ (T-Case resδ₁ δ₁ bsδ₁) (T-Case resδ₂ δ₂ bsδ₂) with typing-uniqueness δ₁ δ₂
  ... | refl
    rewrite unique-Γ⊢τ resδ₁ resδ₂
          | unique-Γ⊢ε⦂τ δ₁ δ₂
          | unique-bs bsδ₁ bsδ₂
          = refl
  unique-Γ⊢ε⦂τ (T-Con refl δ₁ adtτ₁) (T-Con refl δ₂ adtτ₂)
    rewrite unique-Γ⊢ε⦂τ δ₁ δ₂
          | unique-Γ⊢τ adtτ₁ adtτ₂
          = refl
  unique-Γ⊢ε⦂τ (T-SubW <:₁ εδ₁) (T-SubW <:₂ εδ₂) with typing-uniqueness εδ₁ εδ₂
  ... | refl
    rewrite unique-<: <:₁ <:₂
          | unique-Γ⊢ε⦂τ εδ₁ εδ₂
          = refl

  unique-<: : Irrelevant ([ θ ] Γ ⊢ τ' <: τ)
  unique-<: (ST-Base is-just₁ τ'δ₁ τδ₁) (ST-Base is-just₂ τ'δ₂ τδ₂)
    rewrite irrelevant (λ _ _ → refl) is-just₁ is-just₂
          | unique-Γ⊢τ τ'δ₁ τ'δ₂
          | unique-Γ⊢τ τδ₁ τδ₂
          = refl
  unique-<: (ST-Arr <:₁₁ <:₂₁ δ₁₁ δ₂₁) (ST-Arr <:₁₂ <:₂₂ δ₁₂ δ₂₂)
    rewrite unique-<: <:₁₁ <:₁₂
          | unique-<: <:₂₁ <:₂₂
          | unique-Γ⊢τ δ₁₁ δ₁₂
          | unique-Γ⊢τ δ₂₁ δ₂₂
          = refl

  unique-cons : ∀ {cons : ADTCons nₐ ℓ}
              → Irrelevant (All ([ θ ] Γ ⊢_) cons)
  unique-cons [] [] = refl
  unique-cons (δ₁ ∷ δs₁) (δ₂ ∷ δs₂)
    rewrite unique-Γ⊢τ δ₁ δ₂
          | unique-cons δs₁ δs₂
          = refl

  unique-bs : ∀ {cons : ADTCons nₐ ℓ} {bs}
            → Irrelevant (BranchesHaveType θ Γ cons bs τ)
  unique-bs NoBranches NoBranches = refl
  unique-bs (OneMoreBranch εδ₁ δs₁) (OneMoreBranch εδ₂ δs₂)
    rewrite unique-Γ⊢ε⦂τ εδ₁ εδ₂
          | unique-bs δs₁ δs₂
          = refl
