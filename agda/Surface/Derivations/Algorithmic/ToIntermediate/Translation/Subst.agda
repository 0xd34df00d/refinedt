module Surface.Derivations.Algorithmic.ToIntermediate.Translation.Subst where

open import Relation.Binary.PropositionalEquality using (refl)

open import Intermediate.Syntax.Renaming as IR
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

subst-[Γ]⊢τ : (Γok₁ Γok₂ : Γˢ ok[ θˢ , E ])
            → [ θⁱ ] μ-Γ Γok₁ ⊢ τⁱ
            → [ θⁱ ] μ-Γ Γok₂ ⊢ τⁱ
subst-[Γ]⊢τ Γok₁ Γok₂ δ with refl ← unique-Γok Γok₁ Γok₂ = δ


-- Special case helpers
subst-Γ⊢ε⦂[τ₁]⇒[τ₂] : (τ₁δ₁ τ₁δ₂ : Γˢ ⊢[ θˢ , E ] τ₁ˢ)
                    → (τ₂δ₁ τ₂δ₂ : Γˢ ⊢[ θˢ , E ] τ₂ˢ)
                    → [ θⁱ ] Γⁱ ⊢ εⁱ ⦂ μ-τ τ₁δ₁ ⇒ IR.weaken-τ (μ-τ τ₂δ₁)
                    → [ θⁱ ] Γⁱ ⊢ εⁱ ⦂ μ-τ τ₁δ₂ ⇒ IR.weaken-τ (μ-τ τ₂δ₂)
subst-Γ⊢ε⦂[τ₁]⇒[τ₂] τ₁δ₁ τ₁δ₂ τ₂δ₁ τ₂δ₂ δ
  with refl ← unique-Γ⊢τ τ₁δ₁ τ₁δ₂
     | refl ← unique-Γ⊢τ τ₂δ₁ τ₂δ₂
     = δ
