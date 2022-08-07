{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Uniqueness where

open import Data.Maybe.Relation.Unary.Any using (irrelevant)
open import Data.Vec as V
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary using (Irrelevant)

open import Surface.Syntax
open import Surface.Syntax.Injectivity
open import Surface.Syntax.Membership
open import Surface.Syntax.Renaming.Injectivity
open import Surface.Derivations.Algorithmic

∈-uniqueness : τ₁ ∈ Γ at ι
             → τ₂ ∈ Γ at ι
             → τ₁ ≡ τ₂
∈-uniqueness (∈-zero refl) (∈-zero ≡-prf) = sym ≡-prf
∈-uniqueness (∈-suc refl ∈₁) (∈-suc ≡-prf ∈₂) rewrite ∈-uniqueness ∈₁ ∈₂ = sym ≡-prf

typing-uniqueness : Γ ⊢[ θ , φ of not-t-sub ] ε ⦂ τ₁
                  → Γ ⊢[ θ , φ of not-t-sub ] ε ⦂ τ₂
                  → τ₁ ≡ τ₂
typing-uniqueness (T-Unit _) (T-Unit _) = refl
typing-uniqueness (T-Var _ ∈₁) (T-Var _ ∈₂) = ∈-uniqueness ∈₁ ∈₂
typing-uniqueness (T-Abs δ₁) (T-Abs δ₂) rewrite typing-uniqueness δ₁ δ₂ = refl
typing-uniqueness (T-App δ₁ _ refl) (T-App δ₂ _ refl) rewrite ⇒-inj₂ (typing-uniqueness δ₁ δ₂) = refl
typing-uniqueness (T-Case _ _ _) (T-Case _ _ _) = refl
typing-uniqueness (T-Con _ _ _) (T-Con _ _ _) = refl


unique-∈ : Irrelevant (τ ∈ Γ at ι)
unique-∈ (∈-zero refl) (∈-zero refl) = refl
unique-∈ (∈-suc refl ∈₁) (∈-suc ≡-prf ∈₂)
  with refl ← weaken-τ-injective ≡-prf
     | refl ← ≡-prf
  rewrite unique-∈ ∈₁ ∈₂
        = refl

mutual
  unique-Γok : Irrelevant (Γ ok[ θ , φ ])
  unique-Γok TCTX-Empty TCTX-Empty = refl
  unique-Γok (TCTX-Bind δ₁ τδ₁) (TCTX-Bind δ₂ τδ₂)
    rewrite unique-Γok δ₁ δ₂
          | unique-Γ⊢τ τδ₁ τδ₂
          = refl

  unique-Γ⊢τ : Irrelevant (Γ ⊢[ θ , φ ] τ)
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

  unique-Γ⊢τ-if-φ : Irrelevant (Γ ⊢[ θ , φ ] τ ?if φ)
  unique-Γ⊢τ-if-φ omitted omitted = refl
  unique-Γ⊢τ-if-φ (enriched τδ₁) (enriched τδ₂) = cong enriched (unique-Γ⊢τ τδ₁ τδ₂)

  unique-Γ⊢ε⦂τ : Irrelevant (Γ ⊢[ θ , φ of κ ] ε ⦂ τ)
  unique-Γ⊢ε⦂τ (T-Unit Γok₁ ⦃ Γ⊢τ-?if₁ ⦄) (T-Unit Γok₂ ⦃ Γ⊢τ-?if₂ ⦄)
    rewrite unique-Γok Γok₁ Γok₂
          | unique-Γ⊢τ-if-φ Γ⊢τ-?if₁ Γ⊢τ-?if₂
          = refl
  unique-Γ⊢ε⦂τ (T-Var Γok₁ ∈₁ ⦃ Γ⊢τ-?if₁ ⦄) (T-Var Γok₂ ∈₂ ⦃ Γ⊢τ-?if₂ ⦄)
    rewrite unique-Γok Γok₁ Γok₂
          | unique-∈ ∈₁ ∈₂
          | unique-Γ⊢τ-if-φ Γ⊢τ-?if₁ Γ⊢τ-?if₂
          = refl
  unique-Γ⊢ε⦂τ (T-Abs δ₁ ⦃ Γ⊢τ₁⇒τ₂-?if₁ ⦄) (T-Abs δ₂ ⦃ Γ⊢τ₁⇒τ₂-?if₂ ⦄)
    rewrite unique-Γ⊢ε⦂τ δ₁ δ₂
          | unique-Γ⊢τ-if-φ Γ⊢τ₁⇒τ₂-?if₁ Γ⊢τ₁⇒τ₂-?if₂
          = refl
  unique-Γ⊢ε⦂τ (T-App δ₁₁ (T-Sub δ₂₁ <:₁ ⦃ Γ⊢τ₂-?if₁ ⦄) refl ⦃ Γ⊢τ-?if₁ ⦄) (T-App δ₁₂ (T-Sub δ₂₂ <:₂ ⦃ Γ⊢τ₂-?if₂ ⦄) resτ-≡₂ ⦃ Γ⊢τ-?if₂ ⦄)
    with refl ← typing-uniqueness δ₁₁ δ₁₂
       | refl ← typing-uniqueness δ₂₁ δ₂₂
       | refl ← resτ-≡₂
    rewrite unique-Γ⊢ε⦂τ δ₁₁ δ₁₂
          | unique-Γ⊢ε⦂τ δ₂₁ δ₂₂
          | unique-<: <:₁ <:₂
          | unique-Γ⊢τ-if-φ Γ⊢τ-?if₁ Γ⊢τ-?if₂
          | unique-Γ⊢τ-if-φ Γ⊢τ₂-?if₁ Γ⊢τ₂-?if₂
          = refl
  unique-Γ⊢ε⦂τ (T-Case resδ₁ δ₁ bsδ₁) (T-Case resδ₂ δ₂ bsδ₂)
    rewrite unique-Γ⊢τ resδ₁ resδ₂
          | unique-Γ⊢ε⦂τ δ₁ δ₂
          | unique-bs bsδ₁ bsδ₂
          = refl
  unique-Γ⊢ε⦂τ (T-Con <:δ₁ εδ₁ adtτ₁) (T-Con <:δ₂ εδ₂ adtτ₂)
    with refl ← typing-uniqueness εδ₁ εδ₂
    rewrite unique-<: <:δ₁ <:δ₂
          | unique-Γ⊢ε⦂τ εδ₁ εδ₂
          | unique-Γ⊢τ adtτ₁ adtτ₂
          = refl
  unique-Γ⊢ε⦂τ (T-Sub εδ₁ <:₁ ⦃ Γ⊢τ-?if₁ ⦄) (T-Sub εδ₂ <:₂ ⦃ Γ⊢τ-?if₂ ⦄)
    with refl ← typing-uniqueness εδ₁ εδ₂
    rewrite unique-Γ⊢ε⦂τ εδ₁ εδ₂
          | unique-<: <:₁ <:₂
          | unique-Γ⊢τ-if-φ Γ⊢τ-?if₁ Γ⊢τ-?if₂
          = refl

  unique-<: : Irrelevant (Γ ⊢[ θ , φ ] τ' <: τ)
  unique-<: (ST-Base is-just₁ ⦃ δ₁₁ ⦄ ⦃ δ₁₂ ⦄) (ST-Base is-just₂ ⦃ δ₂₁ ⦄ ⦃ δ₂₂ ⦄)
    rewrite irrelevant (λ _ _ → refl) is-just₁ is-just₂
          | unique-Γ⊢τ-if-φ δ₁₁ δ₂₁
          | unique-Γ⊢τ-if-φ δ₁₂ δ₂₂
          = refl
  unique-<: (ST-Arr <:₁₁ <:₂₁ ⦃ δ₁₁ ⦄ ⦃ δ₁₂ ⦄) (ST-Arr <:₁₂ <:₂₂ ⦃ δ₂₁ ⦄ ⦃ δ₂₂ ⦄)
    rewrite unique-<: <:₁₁ <:₁₂
          | unique-<: <:₂₁ <:₂₂
          | unique-Γ⊢τ-if-φ δ₁₁ δ₂₁
          | unique-Γ⊢τ-if-φ δ₁₂ δ₂₂
          = refl
  unique-<: (ST-ADT cons-<:₁) (ST-ADT cons-<:₂)
    rewrite unique-all-subtypes cons-<:₁ cons-<:₂
          = refl

  unique-cons : ∀ {cons : ADTCons nₐ ℓ}
              → Irrelevant (All (Γ ⊢[ θ , φ ]_) cons)
  unique-cons [] [] = refl
  unique-cons (δ₁ ∷ δs₁) (δ₂ ∷ δs₂)
    rewrite unique-Γ⊢τ δ₁ δ₂
          | unique-cons δs₁ δs₂
          = refl

  unique-all-subtypes : {cons' cons : ADTCons nₐ ℓ}
                      → Irrelevant (AllSubtypes Γ θ φ cons' cons)
  unique-all-subtypes {cons' = []}    {[]}    []              [] = refl
  unique-all-subtypes {cons' = _ ∷ _} {_ ∷ _} (τδ₁ ∷ cons-<:₁) (τδ₂ ∷ cons-<:₂)
    rewrite unique-<: τδ₁ τδ₂
          | unique-all-subtypes cons-<:₁ cons-<:₂
          = refl

  unique-bs : ∀ {cons : ADTCons nₐ ℓ} {bs}
            → Irrelevant (BranchesHaveType θ φ Γ cons bs τ)
  unique-bs NoBranches NoBranches = refl
  unique-bs (OneMoreBranch εδ₁ δs₁) (OneMoreBranch εδ₂ δs₂)
    rewrite unique-Γ⊢ε⦂τ εδ₁ εδ₂
          | unique-bs δs₁ δs₂
          = refl
