module Translation.μ-weakening where

open import Data.Fin using (zero; suc)
open import Data.Nat.Base
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Helpers

open import Core.Syntax as C renaming (Γ to Γᶜ; ε to εᶜ)
open import Core.Syntax.Renaming as CR
open import Core.Syntax.Renaming.Distributivity as CR
open import Core.Syntax.Derived as CR
open import Core.Syntax.Derived.Renaming as CR
open import Core.Operational as C
open import Surface.Syntax as S renaming (Γ to Γˢ; Γ' to Γˢ'; τ to τˢ; τ' to τˢ'; ε to εˢ)
open import Surface.Syntax.Subcontext as S
open import Surface.Derivations as S
open import Surface.Theorems.Agreement.Γok.WF
open import Surface.Theorems.Thinning

open import Translation.Untyped
open import Translation.Typed
open import Translation.μ-weakening.Helpers

mutual
  μ-τ-thinning↓-commutes : {Γˢ : S.Ctx (k + ℓ)}
                         → (Γ⊂Γ' : k by Γˢ ⊂' Γˢ')
                         → (Γ'ok : Γˢ' ok[ E ])
                         → (τδ : Γˢ ⊢[ E ] τˢ)
                         → (τδ↓ : Acc _<_ (size-twf τδ))
                         → μ-τ (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok τδ τδ↓) ≡ CR.act-ε (ext-k' k suc) (μ-τ τδ)
  μ-τ-thinning↓-commutes {k = k} Γ⊂Γ' Γ'ok (TWF-TrueRef _) _ = ⌊μ⌋-b-weaken-id k _
  μ-τ-thinning↓-commutes {k = k} {ℓ = ℓ} Γ⊂Γ' Γ'ok (TWF-Base {b = b} {b' = b'} ε₁δ ε₂δ) (acc rec)
    rewrite μ-ε-thinning↓-commutes (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₁δ (rec _ (s≤s (₁≤₂ _ _)))
          | μ-ε-thinning↓-commutes (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₂δ (rec _ (s≤s (₂≤₂ _ _)))
       -- |
          | ⌊μ⌋-b-act-id (k + ℓ) suc b
          | ⌊μ⌋-b-act-id (1 + k + ℓ) suc b
          | ⌊μ⌋-b-act-id (2 + k + ℓ) suc b
       -- |
          | ⌊μ⌋-b-act-id (1 + k + ℓ) (ext-k' (1 + k) suc) b
          | ⌊μ⌋-b-act-id (2 + k + ℓ) (ext-k' (2 + k) suc) b
       -- |
          | ⌊μ⌋-b-act-id (1 + k + ℓ) (ext suc) b'
          | ⌊μ⌋-b-act-id (2 + k + ℓ) (ext suc) b'
          | ⌊μ⌋-b-act-id (3 + k + ℓ) (ext suc) b'
          | ⌊μ⌋-b-act-id (3 + k + ℓ) (ext-k' (3 + k) suc) b'
          | lemma₁ k (μ-ε ε₁δ)
          | lemma₂ k (μ-ε ε₂δ)
          | lemma₃ k (μ-ε ε₂δ)
          = {! !}
  μ-τ-thinning↓-commutes {k = k} Γ⊂Γ' Γ'ok (TWF-Conj τδ₁ τδ₂) (acc rec)
    rewrite act-×-commutes suc (μ-τ τδ₁) (μ-τ τδ₂)
          | μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok τδ₁ (rec _ (s≤s (₁≤₂ _ _)))
          | μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok τδ₂ (rec _ (s≤s (₂≤₂ _ _)))
       -- |
          | CR.act-ε-distr suc (ext-k' (1 + k) suc) (μ-τ τδ₁)
          | CR.act-ε-distr (ext-k' k suc) suc (μ-τ τδ₁)
       -- |
          | CR.act-ε-distr suc suc (μ-τ τδ₂)
          | CR.act-ε-distr (λ ι → suc (suc ι)) (ext-k' (2 + k) suc) (μ-τ τδ₂)
       -- |
          | CR.act-ε-distr (ext-k' k suc) suc (μ-τ τδ₂)
          | CR.act-ε-distr (λ ι → suc (ext-k' k suc ι)) suc (μ-τ τδ₂)
          = refl
  μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok (TWF-Arr τδ₁ τδ₂) (acc rec)
    rewrite μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok τδ₁ (rec _ (s≤s (₁≤₂ _ _)))
          | μ-τ-thinning↓-commutes (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok τδ₁ (rec _ (s≤s (₁≤₂ _ _))))) τδ₂ (rec _ (s≤s (₂≤₂ _ _)))
          = refl
  μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok (TWF-ADT consδs) (acc rec) = {! !}

  μ-ε-thinning↓-commutes : {Γˢ : S.Ctx (k + ℓ)}
                         → (Γ⊂Γ' : k by Γˢ ⊂' Γˢ')
                         → (Γ'ok : Γˢ' ok[ E ])
                         → (εδ : Γˢ ⊢[ E ] εˢ ⦂ τˢ)
                         → (εδ↓ : Acc _<_ (size-t εδ))
                         → μ-ε (Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok εδ εδ↓) ≡ CR.act-ε (ext-k' k suc) (μ-ε εδ)
  μ-ε-thinning↓-commutes = {! !}

μ-τ-thinning-commutes : {Γˢ : S.Ctx (k + ℓ)}
                      → (Γ⊂Γ' : k by Γˢ ⊂' Γˢ')
                      → (Γ'ok : Γˢ' ok[ E ])
                      → (τδ : Γˢ ⊢[ E ] τˢ)
                      → μ-τ (Γ⊢τ-thinning Γ⊂Γ' Γ'ok τδ) ≡ CR.act-ε (ext-k' k suc) (μ-τ τδ)
μ-τ-thinning-commutes Γ⊂Γ' Γ'ok τδ = μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok τδ (<-wellFounded _)

μ-τ-weakening-commutes : (Γok : Γˢ ok[ E ])
                       → (τ'δ : Γˢ ⊢[ E ] τˢ')
                       → (τδ : Γˢ ⊢[ E ] τˢ)
                       → μ-τ (Γ⊢τ-weakening Γok τ'δ τδ) ≡ CR.weaken-ε (μ-τ τδ)
μ-τ-weakening-commutes Γok τ'δ = μ-τ-thinning-commutes ignore-head (TCTX-Bind Γok τ'δ)
