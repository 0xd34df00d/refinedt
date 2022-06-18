module Surface.Derivations.Algorithmic.ToIntermediate.Translation.Subst where

open import Relation.Binary.PropositionalEquality using (refl)

open import Surface.Derivations.Algorithmic.Theorems.Uniqueness

open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Aliases
open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Typed

subst-Γ⊢ε⦂[τ] : (τδ₁ τδ₂ : Γˢ ⊢[ θˢ , E ] τˢ)
              → [ θⁱ ] Γⁱ ⊢ εⁱ ⦂ μ-τ τδ₁
              → [ θⁱ ] Γⁱ ⊢ εⁱ ⦂ μ-τ τδ₂
subst-Γ⊢ε⦂[τ] τδ₁ τδ₂ δ with refl ← unique-Γ⊢τ τδ₁ τδ₂ = δ

subst-[Γ]⊢ε⦂τ : (Γok₁ Γok₂ : Γˢ ok[ θˢ , E ])
              → [ θⁱ ] μ-Γ Γok₁ ⊢ εⁱ ⦂ τⁱ
              → [ θⁱ ] μ-Γ Γok₂ ⊢ εⁱ ⦂ τⁱ
subst-[Γ]⊢ε⦂τ Γok₁ Γok₂ δ with refl ← unique-Γok Γok₁ Γok₂ = δ
