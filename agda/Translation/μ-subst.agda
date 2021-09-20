{-# OPTIONS --allow-unsolved-metas #-}

module Translation.μ-subst where

open import Data.Fin.Base using (zero; suc)
open import Data.Nat.Base using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans)

open import Core.Syntax as C renaming (Γ to Γᶜ; ε to εᶜ; τ to τᶜ)
open import Core.Syntax.Renaming as CR
open import Core.Syntax.Substitution as CS
open import Surface.Syntax as S renaming (Γ to Γˢ;
                                          τ to τˢ; τ' to τ'ˢ; τ₁ to τ₁ˢ; τ₁' to τ₁'ˢ; τ₂ to τ₂ˢ; σ to σˢ;
                                          ε to εˢ; ε' to ε'ˢ; ε₁ to ε₁ˢ; ε₂ to ε₂ˢ)
open import Surface.Syntax.CtxSuffix as S
open import Surface.Syntax.Substitution as SS hiding (ctx-idx)
open import Surface.Derivations.Algorithmic as S
open import Surface.Theorems.Substitution as S

open import Translation.Untyped
open import Translation.Typed

ctx-idx : ∀ k → Fin (suc (k + ℓ))
ctx-idx zero = zero
ctx-idx (suc k) = suc (ctx-idx k)

[_↦<_]_ : ∀ ℓ
        → (ε : CExpr ℓ) → CExpr (suc k + ℓ) → CExpr (k + ℓ)
[_↦<_]_ {k = k} _ ε τ = [ ctx-idx k ↦ CR.weaken-ε-k _ ε ] τ

mutual
  μ-τ-sub-commutes : (Δ : ,-CtxSuffix ℓ σˢ k)
                   → (argδ : Γˢ ⊢[ E of κ ] εˢ ⦂ σˢ)
                   → (domδ : Γˢ ,σ, Δ ⊢[ E ] τˢ)
                   → (codδ : Γˢ ++ [↦Δ εˢ ] Δ ⊢[ E ] [ ℓ ↦τ< εˢ ] τˢ)
                   → μ-τ codδ ≡ [ ℓ ↦< μ-ε argδ ] μ-τ domδ
  μ-τ-sub-commutes Δ argδ (TWF-TrueRef {b = BUnit} Γok) (TWF-TrueRef Γok₂) = refl
  μ-τ-sub-commutes Δ argδ (TWF-Base ε₁δ₁ ε₂δ₁) (TWF-Base ε₁δ₂ ε₂δ₂) = {! !}
  μ-τ-sub-commutes Δ argδ (TWF-Conj domδ domδ₁) (TWF-Conj codδ codδ₁) = {! !}
  μ-τ-sub-commutes Δ argδ (TWF-Arr domδ domδ₁) (TWF-Arr codδ codδ₁) = {! !}
  μ-τ-sub-commutes Δ argδ (TWF-ADT consδs) (TWF-ADT consδs₁) = {! !}

μ-τ-sub-front-commutes : (argδ : Γˢ ⊢[ E of κ ] ε₂ˢ ⦂ τ₁ˢ)
                       → (codδ : Γˢ , τ₁ˢ ⊢[ E ] τ₂ˢ)
                       → (resτδ : Γˢ ⊢[ E ] [ zero ↦τ ε₂ˢ ] τ₂ˢ)
                       → μ-τ resτδ ≡ [ zero ↦  μ-ε argδ ] μ-τ codδ
μ-τ-sub-front-commutes argδ codδ resτδ = μ-τ-sub-commutes [ _ ] argδ codδ {! !}
