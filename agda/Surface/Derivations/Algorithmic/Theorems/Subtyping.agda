module Surface.Derivations.Algorithmic.Theorems.Subtyping where

open import Surface.Syntax
open import Surface.Derivations.Algorithmic

<:-reflexive : Γ ⊢[ θ , E ] τ
             → Γ ⊢[ θ , E ] τ <: τ
<:-reflexive {θ = θ} {τ = ⟨ _ ∣ _ ⟩} τδ = ST-Base (Oracle.<:-refl θ _ _ _) (enriched τδ) (enriched τδ)
<:-reflexive {τ = _ ⇒ _} τ₁⇒τ₂δ@(TWF-Arr τ₁δ τ₂δ)
  = ST-Arr (<:-reflexive τ₁δ) (<:-reflexive τ₂δ) (enriched τ₁⇒τ₂δ) (enriched τ₁⇒τ₂δ)
<:-reflexive {τ = ⊍ _} τδ = ST-ADT (enriched τδ)
