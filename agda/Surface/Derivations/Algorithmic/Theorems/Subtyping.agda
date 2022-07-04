module Surface.Derivations.Algorithmic.Theorems.Subtyping where

open import Data.Product renaming (_,_ to ⟨_,_⟩)

open import Surface.Syntax
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Agreement

<:-reflexive : Γ ⊢[ θ , φ ] τ
             → Γ ⊢[ θ , φ ] τ <: τ
<:-reflexive {θ = θ} {τ = ⟨ _ ∣ _ ⟩} τδ = ST-Base (Oracle.<:-refl θ _ _ _) (as-enrichment τδ) (as-enrichment τδ)
<:-reflexive {τ = _ ⇒ _} τ₁⇒τ₂δ@(TWF-Arr τ₁δ τ₂δ)
  = ST-Arr (<:-reflexive τ₁δ) (<:-reflexive τ₂δ) (as-enrichment τ₁⇒τ₂δ) (as-enrichment τ₁⇒τ₂δ)
<:-reflexive {τ = ⊍ _} τδ = ST-ADT (as-enrichment τδ)

as-sub : ∃[ κ ] (Γ ⊢[ θ , φ of κ ] ε ⦂ τ)
       → Γ ⊢[ θ , φ of t-sub ] ε ⦂ τ
as-sub ⟨ t-sub , εδ ⟩ = εδ
as-sub ⟨ not-t-sub , εδ ⟩
  = let Γ⊢τ = Γ⊢ε⦂τ-⇒-Γ⊢τ εδ
     in T-Sub εδ Γ⊢τ (<:-reflexive Γ⊢τ)

Γ⊢τ'<:τ-⇒-Γ⊢τ₀⇒τ'<:τ₀⇒τ : Γ ⊢[ θ , φ ] τ₀
                        → Γ , τ₀ ⊢[ θ , φ ] τ' <: τ
                        → Γ ⊢[ θ , φ ] τ₀ ⇒ τ' <: τ₀ ⇒ τ
Γ⊢τ'<:τ-⇒-Γ⊢τ₀⇒τ'<:τ₀⇒τ {φ = M} τ₀δ τ'<:τ = ST-Arr (<:-reflexive τ₀δ) τ'<:τ omitted omitted
Γ⊢τ'<:τ-⇒-Γ⊢τ₀⇒τ'<:τ₀⇒τ {φ = E} τ₀δ τ'<:τ
  = let τ₀⇒τδ  = Γ,τ₁⊢τ₂-⇒-Γ⊢τ₁⇒τ₂ (Γ⊢τ'<:τ-⇒-Γ⊢τ τ'<:τ)
        τ₀⇒τ'δ = Γ,τ₁⊢τ₂-⇒-Γ⊢τ₁⇒τ₂ (Γ⊢τ'<:τ-⇒-Γ⊢τ' τ'<:τ)
     in ST-Arr (<:-reflexive τ₀δ) τ'<:τ (enriched τ₀⇒τ'δ) (enriched τ₀⇒τδ)