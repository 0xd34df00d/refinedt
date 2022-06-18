module Surface.Derivations.Algorithmic.ToIntermediate.Translation.Subst where

open import Relation.Binary.PropositionalEquality using (refl)

open import Surface.Syntax as S renaming (Γ to Γˢ;
                                          b to bˢ; ρ to ρˢ;
                                          τ to τˢ; τ' to τ'ˢ; σ to σˢ;
                                          τ₁ to τ₁ˢ; τ₁' to τ₁'ˢ;
                                          τ₂ to τ₂ˢ; τ₂' to τ₂'ˢ;
                                          ε to εˢ; ε' to ε'ˢ; ε₁ to ε₁ˢ; ε₂ to ε₂ˢ)
open import Surface.Derivations.Algorithmic as S renaming (θ to θˢ)
open import Surface.Derivations.Algorithmic.Theorems.Uniqueness

open import Intermediate.Syntax as I renaming (Γ to Γⁱ;
                                               τ to τⁱ; τ' to τ'ⁱ; σ to σⁱ;
                                               τ₁ to τ₁ⁱ; τ₁' to τ₁'ⁱ;
                                               τ₂ to τ₂ⁱ; τ₂' to τ₂'ⁱ;
                                               ε to εⁱ; ε' to ε'ⁱ; ε₁ to ε₁ⁱ; ε₂ to ε₂ⁱ)
open import Intermediate.Derivations.Algorithmic as I renaming (θ to θⁱ)

open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Typed

subst-Γ⊢ε⦂[τ] : (τδ₁ τδ₂ : Γˢ ⊢[ θˢ , E ] τˢ)
              → [ θⁱ ] Γⁱ ⊢ εⁱ ⦂ μ-τ τδ₁
              → [ θⁱ ] Γⁱ ⊢ εⁱ ⦂ μ-τ τδ₂
subst-Γ⊢ε⦂[τ] τδ₁ τδ₂ δ with refl ← unique-Γ⊢τ τδ₁ τδ₂ = δ

subst-[Γ]⊢ε⦂τ : (Γok₁ Γok₂ : Γˢ ok[ θˢ , E ])
              → [ θⁱ ] μ-Γ Γok₁ ⊢ εⁱ ⦂ τⁱ
              → [ θⁱ ] μ-Γ Γok₂ ⊢ εⁱ ⦂ τⁱ
subst-[Γ]⊢ε⦂τ Γok₁ Γok₂ δ with refl ← unique-Γok Γok₁ Γok₂ = δ
