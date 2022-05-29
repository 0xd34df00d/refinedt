{-# OPTIONS --safe #-}

module Surface.Translation.SubstUnique where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)

open import Core.Syntax as C renaming (Γ to Γᶜ; ε to εᶜ; τ to τᶜ)
open import Core.Derivations as C renaming (_⊢_⦂_ to _⊢ᶜ_⦂_)
open import Surface.Syntax as S renaming (Γ to Γˢ;
                                          τ to τˢ; τ' to τ'ˢ; τ₁ to τ₁ˢ; τ₂ to τ₂ˢ;
                                          ε to εˢ)
open import Surface.Derivations.Algorithmic as S
open import Surface.Derivations.Algorithmic.Theorems.Uniqueness

open import Surface.Translation.Typed

subst-Γ : (Γok₁ Γok₂ : Γˢ ok[ θ , E ])
        → μ-Γ Γok₁ ⊢ᶜ εᶜ ⦂ τᶜ
        → μ-Γ Γok₂ ⊢ᶜ εᶜ ⦂ τᶜ
subst-Γ _ _ = subst (_⊢ᶜ _ ⦂ _) (cong μ-Γ (unique-Γok _ _))

subst-τ : (Γ⊢τ₁ Γ⊢τ₂ : Γˢ ⊢[ θ , E ] τˢ)
        → Γᶜ ⊢ᶜ εᶜ ⦂ μ-τ Γ⊢τ₁
        → Γᶜ ⊢ᶜ εᶜ ⦂ μ-τ Γ⊢τ₂
subst-τ Γ⊢τ₁ Γ⊢τ₂ = subst (_ ⊢ᶜ _ ⦂_) (cong μ-τ (unique-Γ⊢τ Γ⊢τ₁ Γ⊢τ₂))

μ-ε-cong-unique : (εδ₁ : Γˢ ⊢[ θ , E of not-t-sub ] εˢ ⦂ τ₁ˢ)
                → (εδ₂ : Γˢ ⊢[ θ , E of not-t-sub ] εˢ ⦂ τ₂ˢ)
                → μ-ε εδ₁ ≡ μ-ε εδ₂
μ-ε-cong-unique εδ₁ εδ₂ with refl ← typing-uniqueness εδ₁ εδ₂ = cong μ-ε (unique-Γ⊢ε⦂τ εδ₁ εδ₂)

μ-τ-cong-unique : (τδ₁ τδ₂ : Γˢ ⊢[ θ , E ] τˢ)
                → μ-τ τδ₁ ≡ μ-τ τδ₂
μ-τ-cong-unique τδ₁ τδ₂ = cong μ-τ (unique-Γ⊢τ τδ₁ τδ₂)
