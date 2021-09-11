{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

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

typing-uniqueness : Γ ⊢[ φ ] ε ⦂ τ₁
                  → Γ ⊢[ φ ] ε ⦂ τ₂
                  → τ₁ ≡ τ₂
typing-uniqueness (T-Unit _) (T-Unit _) = refl
typing-uniqueness (T-Var _ ∈₁) (T-Var _ ∈₂) = ∈-uniqueness ∈₁ ∈₂
typing-uniqueness (T-Abs _ δ₁) (T-Abs _ δ₂) rewrite typing-uniqueness δ₁ δ₂ = refl
typing-uniqueness (T-App δ₁ _ _ refl _) (T-App δ₂ _ _ refl _) rewrite ⇒-inj₂ (typing-uniqueness δ₁ δ₂) = refl
typing-uniqueness (T-Case resδ δ₁ (OneMoreBranch εδ₁ _)) (T-Case resδ₁ δ₂ (OneMoreBranch εδ₂ _)) with typing-uniqueness δ₁ δ₂
... | refl = weaken-τ-injective (typing-uniqueness εδ₁ εδ₂)
typing-uniqueness (T-Con _ _ _) (T-Con _ _ _) = refl


Unique : ∀ A → Set
Unique Deriv = ∀ (δ₁ δ₂ : Deriv)
               → δ₁ ≡ δ₂

unique-∈ : Unique (τ ∈ Γ at ι)
unique-∈ (∈-zero refl) (∈-zero refl) = refl
unique-∈ (∈-suc {τ = τ₁} refl ∈₁) (∈-suc {τ = τ₂} ≡-prf ∈₂) with weaken-τ-injective ≡-prf | ≡-prf
... | refl | refl rewrite unique-∈ ∈₁ ∈₂ = refl

mutual
  unique-Γok : Unique (Γ ok[ φ ])
  unique-Γok TCTX-Empty TCTX-Empty = refl
  unique-Γok (TCTX-Bind δ₁ τδ₁) (TCTX-Bind δ₂ τδ₂)
    rewrite unique-Γok δ₁ δ₂
          | unique-Γ⊢τ τδ₁ τδ₂
          = refl

  unique-Γ⊢τ : Unique (Γ ⊢[ φ ] τ)
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

  unique-Γ⊢ε⦂τ : Unique (Γ ⊢[ φ ] ε ⦂ τ)
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
  unique-Γ⊢ε⦂τ (T-App δ₁₁ δ₂₁ <:₁ refl resτδ₁) (T-App δ₁₂ δ₂₂ <:₂ resτ-≡₂ resτδ₂) = {! !}
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

  unique-cons : ∀ {cons : ADTCons nₐ ℓ}
              → Unique (All (Γ ⊢[ φ ]_) cons)
  unique-cons [] [] = refl
  unique-cons (δ₁ ∷ δs₁) (δ₂ ∷ δs₂)
    rewrite unique-Γ⊢τ δ₁ δ₂
          | unique-cons δs₁ δs₂
          = refl

  unique-bs : ∀ {cons : ADTCons nₐ ℓ} {bs}
            → Unique (BranchesHaveType φ Γ cons bs τ)
  unique-bs NoBranches NoBranches = refl
  unique-bs (OneMoreBranch εδ₁ δs₁) (OneMoreBranch εδ₂ δs₂)
    rewrite unique-Γ⊢ε⦂τ εδ₁ εδ₂
          | unique-bs δs₁ δs₂
          = refl
