{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Agreement.TypeWellFormedness.Enriched where

open import Surface.Syntax
open import Surface.Derivations.Algorithmic

Γ⊢ε⦂τ-⇒-Γ⊢τ : Γ ⊢[ θ , E of κ ] ε ⦂ τ
            → Γ ⊢[ θ , E ] τ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Unit _ ⦃ enriched τδ ⦄) = τδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Var _ _ ⦃ enriched τδ ⦄) = τδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Abs _ ⦃ enriched τδ ⦄) = τδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-App _ _ _ ⦃ enriched τδ ⦄) = τδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Case resδ _ _) = resδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Con _ _ adtτ) = adtτ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Sub _ _ ⦃ enriched τδ ⦄) = τδ
