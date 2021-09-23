{-# OPTIONS --allow-unsolved-metas #-}

module Translation.μ-subst where

open import Data.Fin.Base using (zero; suc; raise)
open import Data.Nat.Base using (zero; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; subst; sym; trans; cong)
open Eq.≡-Reasoning

open import Core.Syntax as C renaming (Γ to Γᶜ; ε to εᶜ; τ to τᶜ)
open import Core.Syntax.Derived as C
open import Core.Syntax.Renaming as CR
open import Core.Syntax.Substitution as CS
open import Core.Syntax.Derived.Substitution as CS
open import Surface.Syntax as S renaming (Γ to Γˢ;
                                          τ to τˢ; τ' to τ'ˢ; τ₁ to τ₁ˢ; τ₁' to τ₁'ˢ; τ₂ to τ₂ˢ; σ to σˢ;
                                          ε to εˢ; ε' to ε'ˢ; ε₁ to ε₁ˢ; ε₂ to ε₂ˢ)
open import Surface.Syntax.CtxSuffix as S
open import Surface.Syntax.Renaming as SR
open import Surface.Syntax.Substitution as SS
open import Surface.Derivations.Algorithmic as S
open import Surface.Theorems.Substitution as S

open import Translation.Untyped
open import Translation.Typed

ctx-idxᶜ : ∀ k → Fin (suc (k + ℓ))
ctx-idxᶜ zero = zero
ctx-idxᶜ (suc k) = suc (ctx-idxᶜ k)

[_↦<_]_ : ∀ ℓ
        → (ε : CExpr ℓ) → CExpr (suc k + ℓ) → CExpr (k + ℓ)
[_↦<_]_ {k = k} _ ε τ = [ ctx-idxᶜ k ↦ CR.weaken-ε-k _ ε ] τ

mutual
  μ-τ-sub-commutes : (Δ : ,-CtxSuffix ℓ σˢ k)
                   → (argδ : Γˢ ⊢[ E of κ ] εˢ ⦂ σˢ)
                   → (domδ : Γˢ ,σ, Δ ⊢[ E ] τˢ)
                   → (codδ : Γˢ ++ [↦Δ εˢ ] Δ ⊢[ E ] [ ℓ ↦τ< εˢ ] τˢ)
                   → μ-τ codδ ≡ [ ℓ ↦< μ-ε argδ ] μ-τ domδ
  μ-τ-sub-commutes Δ argδ (TWF-TrueRef {b = BUnit} Γok) (TWF-TrueRef Γok₂) = refl
  μ-τ-sub-commutes Δ argδ (TWF-Base ε₁δ₁ ε₂δ₁) (TWF-Base ε₁δ₂ ε₂δ₂) = {! !}
  μ-τ-sub-commutes {ℓ = ℓ} {k = k} Δ argδ (TWF-Conj ρ₁δ₁ ρ₂δ₁) (TWF-Conj ρ₁δ₂ ρ₂δ₂)
    = let ×-comm = act-×-commutes
                    (CS.replace-at (ctx-idxᶜ k) (CR.weaken-ε-k _ (μ-ε argδ)))
                    (μ-τ ρ₁δ₁)
                    (μ-τ ρ₂δ₁)
       in trans rec-commutes (sym ×-comm)
    where
    rec-commutes : ⟨ μ-τ ρ₁δ₂ × μ-τ ρ₂δ₂ ⟩ ≡ ⟨ ([ ℓ ↦< μ-ε argδ ] μ-τ ρ₁δ₁) × ([ ℓ ↦< μ-ε argδ ] μ-τ ρ₂δ₁) ⟩
    rec-commutes
      rewrite μ-τ-sub-commutes Δ argδ ρ₁δ₁ ρ₁δ₂
            | μ-τ-sub-commutes Δ argδ ρ₂δ₁ ρ₂δ₂
            = refl
  μ-τ-sub-commutes {ℓ = ℓ} {k = k} {εˢ = εˢ} Δ argδ (TWF-Arr {τ₂ = τ₂} argδ₁ resδ₁) (TWF-Arr argδ₂ resδ₂)
    = begin
        CΠ (μ-τ argδ₂) (μ-τ resδ₂)
      ≡⟨ cong (λ argδ → CΠ argδ (μ-τ resδ₂)) (μ-τ-sub-commutes Δ argδ argδ₁ argδ₂) ⟩
        CΠ ([ ℓ ↦< μ-ε argδ ] μ-τ argδ₁) (μ-τ resδ₂)
      ≡⟨ cong (CΠ _) resδ-subst-massage ⟩
        CΠ ([ ℓ ↦< μ-ε argδ ] μ-τ argδ₁) ([ ℓ ↦< μ-ε argδ ] μ-τ resδ₁)
      ≡⟨ cong
            (CΠ _)
            (sym (CS.act-ε-extensionality (CS.ext-replace-comm (CR.weaken-ε-k k (μ-ε argδ)) (ctx-idxᶜ k)) (μ-τ resδ₁))) ⟩
        ([ ℓ ↦< μ-ε argδ ] CΠ (μ-τ argδ₁) (μ-τ resδ₁))
      ∎
    where
    resδ-subst-massage : μ-τ resδ₂ ≡ [ ℓ ↦< μ-ε argδ ] μ-τ resδ₁
    resδ-subst-massage
      rewrite SS.act-τ-extensionality (SS.ext-replace-comm (SR.weaken-ε-k k εˢ) (SS.ctx-idx k)) τ₂
            | SR.act-ε-distr (raise k) suc εˢ
            = μ-τ-sub-commutes (Δ , _) argδ resδ₁ resδ₂
  μ-τ-sub-commutes Δ argδ (TWF-ADT consδs₁) (TWF-ADT consδs₂) = {! !}

μ-τ-sub-front-commutes : (argδ : Γˢ ⊢[ E of κ ] ε₂ˢ ⦂ τ₁ˢ)
                       → (codδ : Γˢ , τ₁ˢ ⊢[ E ] τ₂ˢ)
                       → (resτδ : Γˢ ⊢[ E ] [ zero ↦τ ε₂ˢ ] τ₂ˢ)
                       → μ-τ resτδ ≡ [ zero ↦  μ-ε argδ ] μ-τ codδ
μ-τ-sub-front-commutes argδ codδ resτδ = μ-τ-sub-commutes [ _ ] argδ codδ {! !}
