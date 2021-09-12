{-# OPTIONS --safe #-}

module Translation.μ-weakening where

open import Data.Fin using (zero; suc)
open import Data.Nat.Base
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Common.Helpers

open import Core.Syntax as C renaming (Γ to Γᶜ; ε to εᶜ)
open import Core.Syntax.Renaming as CR
open import Core.Syntax.Renaming.Distributivity as CR
open import Core.Syntax.Derived as CR
open import Core.Syntax.Derived.Renaming as CR
open import Core.Operational as C
open import Surface.Syntax as S renaming (Γ to Γˢ; Γ' to Γˢ'; τ to τˢ; τ' to τˢ'; ε to εˢ)
open import Surface.Syntax.Subcontext as S
open import Surface.Syntax.Renaming as SR
open import Surface.Syntax.Substitution.Distributivity
open import Surface.Derivations.Algorithmic as S
open import Surface.Derivations.Algorithmic.Theorems.Agreement.Γok
open import Surface.Derivations.Algorithmic.Theorems.Agreement.Γok.WF
open import Surface.Derivations.Algorithmic.Theorems.Thinning

open import Translation.Untyped
open import Translation.Typed
open import Translation.μ-weakening.Helpers

μ-ε-subst : (eq : τˢ ≡ τˢ')
          → (δ : Γˢ ⊢[ E ] εˢ ⦂ τˢ)
          → μ-ε (subst (λ τ → Γˢ ⊢[ E ] εˢ ⦂ τ) eq δ) ≡ μ-ε δ
μ-ε-subst refl δ = refl

mutual
  μ-<:-thinning↓-commutes : {Γˢ : S.Ctx (k + ℓ)}
                          → (Γ⊂Γ' : k by Γˢ ⊂' Γˢ')
                          → (Γ'ok : Γˢ' ok[ E ])
                          → (δ : Γˢ ⊢[ E ] τˢ <: τˢ')
                          → (δ↓ : Acc _<_ (size-<: δ))
                          → μ-<: (<:-thinning↓ Γ⊂Γ' (enriched Γ'ok) δ δ↓) ≡ CR.act-ε (ext-k' k suc) (μ-<: δ)
  μ-<:-thinning↓-commutes Γ⊂Γ' Γ'ok (ST-Base oracle is-just) (acc rec) = Oracle.thin-ε oracle is-just Γ⊂Γ'
  μ-<:-thinning↓-commutes {k = k} Γ⊂Γ' Γ'ok (ST-Arr <:₁δ <:₂δ (enriched δτ₁⇒τ₂) (enriched δτ₁')) (acc rec)
    rewrite μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok δτ₁⇒τ₂ (rec _ (s≤s (₃≤₄ (size-<: <:₁δ) (size-<: <:₂δ) (size-twf δτ₁⇒τ₂) (size-twf δτ₁'))))
          | μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok δτ₁'   (rec _ (s≤s (₄≤₄ (size-<: <:₁δ) (size-<: <:₂δ) (size-twf δτ₁⇒τ₂) (size-twf δτ₁'))))
          | μ-<:-thinning↓-commutes
                  Γ⊂Γ'
                  Γ'ok
                  <:₁δ
                  (rec _ (s≤s (₁≤₄ (size-<: <:₁δ) (size-<: <:₂δ) (size-twf δτ₁⇒τ₂) (size-twf δτ₁'))))
          | μ-<:-thinning↓-commutes
                  (append-both Γ⊂Γ')
                  (TCTX-Bind Γ'ok (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok δτ₁' (rec _ (s≤s (₄≤₄ (size-<: <:₁δ) (size-<: <:₂δ) (size-twf δτ₁⇒τ₂) (size-twf δτ₁'))))))
                  <:₂δ
                  (rec _ (s≤s (₂≤₄ (size-<: <:₁δ) (size-<: <:₂δ) (size-twf δτ₁⇒τ₂) (size-twf δτ₁'))))
       -- |
          | CR.act-ε-distr suc (ext-k' (1 + k) suc) (μ-τ δτ₁')
          | CR.act-ε-distr (ext-k' k suc) suc (μ-τ δτ₁')
       -- |
          | lemma₅ k (μ-<: <:₂δ)
       -- |
          | CR.act-ε-distr (ext-k' k suc) suc (μ-<: <:₁δ)
          | CR.act-ε-distr (λ ι → suc (ext-k' k suc ι)) suc (μ-<: <:₁δ)
          | CR.act-ε-distr suc suc (μ-<: <:₁δ)
          | CR.act-ε-distr (λ ι → suc (suc ι)) (ext-k' (2 + k) suc) (μ-<: <:₁δ)
          = refl

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
          | ⌊μ⌋-b-act-id (1 + k + ℓ) (CR.ext suc) b'
          | ⌊μ⌋-b-act-id (2 + k + ℓ) (CR.ext suc) b'
          | ⌊μ⌋-b-act-id (3 + k + ℓ) (CR.ext suc) b'
          | ⌊μ⌋-b-act-id (3 + k + ℓ) (ext-k' (3 + k) suc) b'
          | lemma₁ k (μ-ε ε₁δ)
          | lemma₂ k (μ-ε ε₂δ)
          | lemma₃ k (μ-ε ε₂δ)
          | lemma₄ k (μ-ε ε₁δ)
          = refl
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
  μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok (TWF-ADT consδs) (acc rec)
    rewrite μ-cons-thinning↓-commutes Γ⊂Γ' Γ'ok consδs (rec _ ≤-refl)
          = refl

  μ-ε-thinning↓-commutes : {Γˢ : S.Ctx (k + ℓ)}
                         → (Γ⊂Γ' : k by Γˢ ⊂' Γˢ')
                         → (Γ'ok : Γˢ' ok[ E ])
                         → (εδ : Γˢ ⊢[ E ] εˢ ⦂ τˢ)
                         → (εδ↓ : Acc _<_ (size-t εδ))
                         → μ-ε (Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok εδ εδ↓) ≡ CR.act-ε (ext-k' k suc) (μ-ε εδ)
  μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok (T-Unit _) _ = refl
  μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok (T-Var _ _) _ = refl
  μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok (T-Abs arrδ@(TWF-Arr domδ codδ) εδ) (acc rec)
    rewrite μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok arrδ (rec _ (s≤s (₁≤₂ _ (size-t εδ))))
          | μ-ε-thinning↓-commutes
              (append-both Γ⊂Γ')
              (TCTX-Bind Γ'ok (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok domδ (rec _ (s≤s (≤-trans (≤-trans (₁≤₂ _ (size-twf codδ)) (n≤1+n _)) (₁≤₂ _ (size-t εδ)))))))
              εδ
              (rec _ (s≤s (₂≤₂ _ _)))
          = refl
  μ-ε-thinning↓-commutes {k = k} Γ⊂Γ' Γ'ok (T-App {τ₂ = τ₂} {ε₂ = ε₂} ε₁δ ε₂δ <: refl _) (acc rec)
    rewrite ρ-subst-distr-τ-0 (ext-k' k suc) ε₂ τ₂
          | μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok ε₁δ (rec _ (s≤s (₁≤₂ _ _)))
          | μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok ε₂δ (rec _ (s≤s (₂≤₃ (size-t ε₁δ) _ _)))
          | μ-<:-thinning↓-commutes Γ⊂Γ' Γ'ok <: (rec _ (s≤s (₃≤₄ (size-t ε₁δ) (size-t ε₂δ) _ _)))
          = refl
  μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok (T-Case resδ εδ branchesδ) (acc rec)
    rewrite μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok εδ (rec _ (s≤s (₁≤₂ _ _)))
          | μ-branches-thinning↓-commutes Γ⊂Γ' Γ'ok branchesδ (rec _ (s≤s (₃≤₃ (size-t εδ) (size-twf resδ) (size-bs branchesδ))))
          = refl
  μ-ε-thinning↓-commutes {k = k} Γ⊂Γ' Γ'ok (T-Con {ι = ι} {cons = cons} refl εδ adtτ@(TWF-ADT consδs)) (acc rec)
    rewrite μ-ε-subst (SR.cons-lookup-comm (ext-k' k suc) ι cons) (Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok εδ (rec _ (s≤s (₁≤₂ _ _))))
          | μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok εδ (rec _ (s≤s (₁≤₂ _ _)))
          | μ-cons'-thinning↓-commutes Γ⊂Γ' Γ'ok consδs (rec _ (s≤s (₂≤₂ _ _)))
          = refl

  μ-cons'-thinning↓-commutes : {Γˢ : S.Ctx (k + ℓ)}
                             → {cons : S.ADTCons (Mkℕₐ (suc n)) (k + ℓ)}
                             → (Γ⊂Γ' : k by Γˢ ⊂' Γˢ')
                             → (Γ'ok : Γˢ' ok[ E ])
                             → (consδs : All (Γˢ ⊢[ E ]_) cons)
                             → (consδs↓ : Acc _<_ (suc (size-all-cons consδs)))
                             → μ-cons' (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok (TWF-ADT consδs) consδs↓) ≡ CR.act-cons (ext-k' k suc) (μ-cons consδs)
  μ-cons'-thinning↓-commutes Γ⊂Γ' Γ'ok consδs (acc rec) = μ-cons-thinning↓-commutes Γ⊂Γ' Γ'ok consδs (rec _ ≤-refl)

  μ-cons-thinning↓-commutes : {Γˢ : S.Ctx (k + ℓ)}
                            → {cons : S.ADTCons nₐ (k + ℓ)}
                            → (Γ⊂Γ' : k by Γˢ ⊂' Γˢ')
                            → (Γ'ok : Γˢ' ok[ E ])
                            → (consδs : All (Γˢ ⊢[ E ]_) cons)
                            → (consδs↓ : Acc _<_ (size-all-cons consδs))
                            → μ-cons (cons-thinning↓ Γ⊂Γ' Γ'ok consδs consδs↓) ≡ CR.act-cons (ext-k' k suc) (μ-cons consδs)
  μ-cons-thinning↓-commutes Γ⊂Γ' Γ'ok [] (acc rec) = refl
  μ-cons-thinning↓-commutes Γ⊂Γ' Γ'ok (δ ∷ consδs) (acc rec)
    rewrite μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok δ (rec _ (s≤s (₁≤₂ _ _)))
          | μ-cons-thinning↓-commutes Γ⊂Γ' Γ'ok consδs (rec _ (s≤s (₂≤₂ _ _)))
          = refl

  μ-branches-thinning↓-commutes : {Γˢ : S.Ctx (k + ℓ)}
                                → {cons : S.ADTCons nₐ (k + ℓ)}
                                → {bs : S.CaseBranches nₐ (k + ℓ)}
                                → (Γ⊂Γ' : k by Γˢ ⊂' Γˢ')
                                → (Γ'ok : Γˢ' ok[ E ])
                                → (δs : BranchesHaveType E Γˢ cons bs τˢ)
                                → (δs↓ : Acc _<_ (size-bs δs))
                                → μ-branches (branches-thinning↓ Γ⊂Γ' Γ'ok δs δs↓) ≡ CR.act-branches (ext-k' k suc) (μ-branches δs)
  μ-branches-thinning↓-commutes Γ⊂Γ' Γ'ok NoBranches (acc rec) = refl
  μ-branches-thinning↓-commutes Γ⊂Γ' Γ'ok (OneMoreBranch εδ δs) (acc rec) with Γ⊢ε⦂τ-⇒-Γok εδ | Γ⊢ε⦂τ-⇒-Γok-smaller εδ
  ... | TCTX-Bind _ conτδ
      | sub-≤
      rewrite μ-branches-thinning↓-commutes Γ⊂Γ' Γ'ok δs (rec _ (s≤s (₂≤₂ _ _)))
            = refl

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
