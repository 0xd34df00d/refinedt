{-# OPTIONS --safe #-}

open import Surface.Derivations.Algorithmic using (UniquenessOfOracles)

module Surface.Translation.SubstUnique(oracles-equal : UniquenessOfOracles) where

open import Relation.Binary.PropositionalEquality using (subst; cong)

open import Core.Syntax as C renaming (Γ to Γᶜ; ε to εᶜ; τ to τᶜ)
open import Core.Derivations as C renaming (_⊢_⦂_ to _⊢ᶜ_⦂_)
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; τ' to τ'ˢ; ε to εˢ)
open import Surface.Derivations.Algorithmic as S
open import Surface.Derivations.Algorithmic.Theorems.Uniqueness(oracles-equal)

open import Surface.Translation.Typed

subst-Γ : (Γok₁ Γok₂ : Γˢ ok[ E ])
        → μ-Γ Γok₁ ⊢ᶜ εᶜ ⦂ τᶜ
        → μ-Γ Γok₂ ⊢ᶜ εᶜ ⦂ τᶜ
subst-Γ _ _ = subst (_⊢ᶜ _ ⦂ _) (cong μ-Γ (unique-Γok _ _))

subst-τ : (Γ⊢τ₁ Γ⊢τ₂ : Γˢ ⊢[ E ] τˢ)
        → Γᶜ ⊢ᶜ εᶜ ⦂ μ-τ Γ⊢τ₁
        → Γᶜ ⊢ᶜ εᶜ ⦂ μ-τ Γ⊢τ₂
subst-τ Γ⊢τ₁ Γ⊢τ₂ = subst (_ ⊢ᶜ _ ⦂_) (cong μ-τ (unique-Γ⊢τ Γ⊢τ₁ Γ⊢τ₂))
