{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Subtyping where

open import Data.Product renaming (_,_ to ⟨_,_⟩)

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Agreement

<:-reflexive : Γ ⊢[ θ ] τ <: τ
<:-reflexive {θ = θ} {τ = ⟨ _ ∣ _ ⟩} = ST-Base (Oracle.<:-refl θ _ _ _)
<:-reflexive {τ = _ ⇒ _} = ST-Arr <:-reflexive <:-reflexive
<:-reflexive {τ = ⊍ _} = ST-ADT

as-sub : ∃[ κ ] (Γ ⊢[ θ , φ of κ ] ε ⦂ τ)
       → Γ ⊢[ θ , φ of t-sub ] ε ⦂ τ
as-sub ⟨ t-sub , εδ ⟩ = εδ
as-sub ⟨ not-t-sub , εδ ⟩
  = let Γ⊢τ = Γ⊢ε⦂τ-⇒-Γ⊢τ εδ
     in T-Sub εδ Γ⊢τ <:-reflexive

Γ⊢τ'<:τ-⇒-Γ⊢τ₀⇒τ'<:τ₀⇒τ : Γ , τ₀ ⊢[ θ ] τ' <: τ
                        → Γ ⊢[ θ ] τ₀ ⇒ τ' <: τ₀ ⇒ τ
Γ⊢τ'<:τ-⇒-Γ⊢τ₀⇒τ'<:τ₀⇒τ τ'<:τ = ST-Arr <:-reflexive τ'<:τ

<:-narrowing : {σ σ' : SType ℓ} {Γ : Ctx ℓ}
             → (σ-<:δ : Γ ⊢[ θ ] σ' <: σ)
             → (Δ : CtxSuffix (suc ℓ) k)
             → Γ , σ  ++ Δ ⊢[ θ ] τ₂' <: τ₂
             → Γ , σ' ++ Δ ⊢[ θ ] τ₂' <: τ₂
<:-narrowing {θ = θ} σ-<:δ Δ (ST-Base is-just) = ST-Base (Oracle.narrowing θ {- TODO σ-<:δ -} is-just)
<:-narrowing σ-<:δ Δ (ST-Arr <:₁δ <:₂δ)
  = let <:₁δ' = <:-narrowing σ-<:δ Δ <:₁δ
     in ST-Arr
          <:₁δ'
          (<:-narrowing σ-<:δ (Δ , _) <:₂δ)
<:-narrowing σ-<:δ Δ ST-ADT = ST-ADT

<:-transitive : ∀ {τ''}
              → Γ ⊢[ θ ] τ'' <: τ'
              → Γ ⊢[ θ ] τ'  <: τ
              → Γ ⊢[ θ ] τ'' <: τ
<:-transitive {θ = θ} (ST-Base is-just') (ST-Base is-just) = ST-Base (Oracle.trans θ is-just' is-just)
<:-transitive (ST-Arr <:₁'δ <:₂'δ) (ST-Arr <:₁δ <:₂δ)
  = ST-Arr
      (<:-transitive <:₁δ <:₁'δ)
      (<:-transitive (<:-narrowing <:₁δ ⊘ <:₂'δ) <:₂δ)
<:-transitive ST-ADT ST-ADT = ST-ADT

as-sub' : Γ ⊢[ θ ] τ' <: τ
        → Γ ⊢[ θ , φ ] τ
        → ∃[ κ ] (Γ ⊢[ θ , φ of κ ] ε ⦂ τ')
        → Γ ⊢[ θ , φ of t-sub ] ε ⦂ τ
as-sub' <:δ τδ ⟨ t-sub , T-Sub εδ _ <:'δ ⟩ = T-Sub εδ τδ (<:-transitive <:'δ <:δ)
as-sub' <:δ τδ ⟨ not-t-sub , εδ ⟩ = T-Sub εδ τδ <:δ
