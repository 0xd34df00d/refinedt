{-# OPTIONS --safe #-}

module Surface.Translation.SubstUnique where

open import Relation.Binary.PropositionalEquality using (subst; cong)

open import Core.Syntax as C renaming (Γ to Γᶜ; ε to εᶜ; τ to τᶜ)
open import Core.Derivations as C renaming (_⊢_⦂_ to _⊢ᶜ_⦂_)
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; τ' to τ'ˢ; ε to εˢ)
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
