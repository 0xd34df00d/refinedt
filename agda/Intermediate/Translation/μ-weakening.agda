{-# OPTIONS --safe #-}

module Intermediate.Translation.μ-weakening where

open import Data.Fin using (zero; suc; raise; #_)
open import Data.Nat.Base
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans; sym)

open import Common.Inequalities
open import Common.Helpers

open import Core.Syntax as C renaming (Γ to Γᶜ; ε to εᶜ)
open import Core.Syntax.Renaming as CR
open import Core.Syntax.Renaming.Distributivity as CR
open import Core.Syntax.Derived as CR
open import Core.Syntax.Derived.Renaming as CR
open import Intermediate.Syntax as I renaming (Γ to Γⁱ; Γ' to Γⁱ'; τ to τⁱ; τ' to τⁱ'; ε to εⁱ)
open import Intermediate.Syntax.CtxSuffix as I renaming (Δ to Δⁱ)
open import Intermediate.Syntax.Subcontext as I
open import Intermediate.Syntax.Renaming as IR
open import Intermediate.Syntax.Substitution.Distributivity
open import Intermediate.Derivations.Algorithmic as I
open import Intermediate.Derivations.Algorithmic.Theorems.Agreement.Γok
open import Intermediate.Derivations.Algorithmic.Theorems.Agreement.Γok.WF
open import Intermediate.Derivations.Algorithmic.Theorems.Helpers
open import Intermediate.Derivations.Algorithmic.Theorems.Thinning
open import Intermediate.Derivations.Algorithmic.Theorems.Uniqueness

open import Intermediate.Translation.SubstUnique
open import Intermediate.Translation.Typed
open import Intermediate.Translation.Untyped
open import Intermediate.Translation.μ-weakening.Helpers

μ-ε-subst : (eq : τⁱ ≡ τⁱ')
          → (δ : [ θ ] Γⁱ ⊢ εⁱ ⦂ τⁱ)
          → μ-ε (subst (λ τ → [ θ ] Γⁱ ⊢ εⁱ ⦂ τ) eq δ) ≡ μ-ε δ
μ-ε-subst refl δ = refl

mutual
  μ-<:-thinning↓-commutes : {Γⁱ : I.Ctx (k + ℓ)}
                          → (Γ⊂Γ' : k by Γⁱ ⊂' Γⁱ')
                          → (Γ'ok : [ θ ] Γⁱ' ok)
                          → (δ : [ θ ] Γⁱ ⊢ τⁱ <: τⁱ')
                          → (δ↓ : Acc _<_ (size-<: δ))
                          → μ-<: (<:-thinning↓ Γ⊂Γ' Γ'ok δ δ↓) ≡ CR.act-ε (ext-k' k suc) (μ-<: δ)
  μ-<:-thinning↓-commutes {θ = θ} Γ⊂Γ' Γ'ok (ST-Base is-just _ _) (acc rec) = Oracle.thin-ε θ is-just Γ⊂Γ'
  μ-<:-thinning↓-commutes {k = k} Γ⊂Γ' Γ'ok arr@(ST-Arr <:₁δ <:₂δ τ₁⇒τ₂'δ τ₁'⇒τ₂δ@(TWF-Arr τ₁'δ _)) (acc rec)
    with τ₁'⇒τ₂δ'@(TWF-Arr τ₁'δ' _) ← Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok τ₁'⇒τ₂δ (rec _ (<₄ (ST-Arr-size-vec arr) (# 3)))
    rewrite μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok τ₁⇒τ₂'δ (rec _ (<₄ (ST-Arr-size-vec arr) (# 2)))
          | μ-<:-thinning↓-commutes
                  Γ⊂Γ'
                  Γ'ok
                  <:₁δ
                  (rec _ (<₄ (ST-Arr-size-vec arr) (# 0)))
          | μ-<:-thinning↓-commutes
                  (append-both Γ⊂Γ')
                  (TCTX-Bind Γ'ok τ₁'δ')
                  <:₂δ
                  (rec _ (<₄ (ST-Arr-size-vec arr) (# 1)))
       -- |
          | trans
              (μ-τ-cong-unique τ₁'δ' (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok τ₁'δ (rec _ (ST-Arr-τ₁'-smaller arr))))
              (μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok τ₁'δ (rec _ (ST-Arr-τ₁'-smaller arr)))
          | CR.act-ε-distr suc (ext-k' (1 + k) suc) (μ-τ τ₁'δ)
          | CR.act-ε-distr (ext-k' k suc) suc (μ-τ τ₁'δ)
       -- |
          | lemma₅ k (μ-<: <:₂δ)
       -- |
          | CR.act-ε-distr (ext-k' k suc) suc (μ-<: <:₁δ)
          | CR.act-ε-distr (λ ι → suc (ext-k' k suc ι)) suc (μ-<: <:₁δ)
          | CR.act-ε-distr suc suc (μ-<: <:₁δ)
          | CR.act-ε-distr (λ ι → suc (suc ι)) (ext-k' (2 + k) suc) (μ-<: <:₁δ)
          = refl

  μ-τ-thinning↓-commutes : {Γⁱ : I.Ctx (k + ℓ)}
                         → (Γ⊂Γ' : k by Γⁱ ⊂' Γⁱ')
                         → (Γ'ok : [ θ ] Γⁱ' ok)
                         → (τδ : [ θ ] Γⁱ ⊢ τⁱ)
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

  μ-ε-thinning↓-commutes : {Γⁱ : I.Ctx (k + ℓ)}
                         → (Γ⊂Γ' : k by Γⁱ ⊂' Γⁱ')
                         → (Γ'ok : [ θ ] Γⁱ' ok)
                         → (εδ : [ θ ] Γⁱ ⊢ εⁱ ⦂ τⁱ)
                         → (εδ↓ : Acc _<_ (size-t εδ))
                         → μ-ε (Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok εδ εδ↓) ≡ CR.act-ε (ext-k' k suc) (μ-ε εδ)
  μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok (T-Unit _) _ = refl
  μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok (T-Var _ _) _ = refl
  μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok (T-Abs arrδ@(TWF-Arr domδ codδ) εδ) (acc rec) with Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok arrδ (rec _ (s≤s (₁≤₂ _ (size-t εδ))))
  ... | TWF-Arr domδ' codδ'
    rewrite trans (cong μ-τ (unique-Γ⊢τ domδ' (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok domδ _))) (μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok domδ (rec _ (s≤s (a<1+[a⊔b]⊔c _ _ (size-t εδ)))))
          | μ-ε-thinning↓-commutes
              (append-both Γ⊂Γ')
              (TCTX-Bind Γ'ok (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok domδ (rec _ (s≤s (≤-trans (≤-trans (₁≤₂ _ (size-twf codδ)) (n≤1+n _)) (₁≤₂ _ (size-t εδ)))))))
              εδ
              (rec _ (s≤s (₂≤₂ _ _)))
          = refl
  μ-ε-thinning↓-commutes {k = k} Γ⊂Γ' Γ'ok (T-App {τ₂ = τ₂} {ε₂ = ε₂} ε₁δ ε₂δ refl _) (acc rec)
    rewrite ρ-subst-distr-τ-0 (ext-k' k suc) ε₂ τ₂
          | μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok ε₁δ (rec _ (s≤s (₁≤₂ _ _)))
          | μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok ε₂δ (rec _ (s≤s (₂≤₃ (size-t ε₁δ) _ _)))
          = refl
  μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok (T-Case resδ εδ branchesδ) (acc rec)
    rewrite μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok εδ (rec _ (s≤s (₁≤₂ _ _)))
          | μ-branches-thinning↓-commutes Γ⊂Γ' Γ'ok branchesδ (rec _ (s≤s (₃≤₃ (size-t εδ) (size-twf resδ) (size-bs branchesδ))))
          = refl
  μ-ε-thinning↓-commutes {k = k} Γ⊂Γ' Γ'ok (T-Con {ι = ι} {cons = cons} refl εδ (TWF-ADT consδs)) (acc rec)
    rewrite μ-ε-subst (IR.cons-lookup-comm (ext-k' k suc) ι cons) (Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok εδ (rec _ (s≤s (₁≤₂ _ _))))
          | μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok εδ (rec _ (s≤s (₁≤₂ _ _)))
          | μ-cons-thinning↓-commutes Γ⊂Γ' Γ'ok consδs (rec _ (s≤s (₂≤₂ _ _)))
          = refl
  μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok (T-SubW <: εδ) (acc rec)
    rewrite μ-ε-thinning↓-commutes  Γ⊂Γ' Γ'ok εδ (rec _ (s≤s (₁≤₂ _ _)))
          | μ-<:-thinning↓-commutes Γ⊂Γ' Γ'ok <: (rec _ (s≤s (₂≤₂ _ _)))
          = refl

  μ-cons-thinning↓-commutes : {Γⁱ : I.Ctx (k + ℓ)}
                            → {cons : I.ADTCons nₐ (k + ℓ)}
                            → (Γ⊂Γ' : k by Γⁱ ⊂' Γⁱ')
                            → (Γ'ok : [ θ ] Γⁱ' ok)
                            → (consδs : All ([ θ ] Γⁱ ⊢_) cons)
                            → (consδs↓ : Acc _<_ (size-all-cons consδs))
                            → μ-cons (cons-thinning↓ Γ⊂Γ' Γ'ok consδs consδs↓) ≡ CR.act-cons (ext-k' k suc) (μ-cons consδs)
  μ-cons-thinning↓-commutes Γ⊂Γ' Γ'ok [] (acc rec) = refl
  μ-cons-thinning↓-commutes Γ⊂Γ' Γ'ok (δ ∷ consδs) (acc rec)
    rewrite μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok δ (rec _ (s≤s (₁≤₂ _ _)))
          | μ-cons-thinning↓-commutes Γ⊂Γ' Γ'ok consδs (rec _ (s≤s (₂≤₂ _ _)))
          = refl

  μ-branches-thinning↓-commutes : {Γⁱ : I.Ctx (k + ℓ)}
                                → {cons : I.ADTCons nₐ (k + ℓ)}
                                → {bs : I.CaseBranches nₐ (k + ℓ)}
                                → (Γ⊂Γ' : k by Γⁱ ⊂' Γⁱ')
                                → (Γ'ok : [ θ ] Γⁱ' ok)
                                → (δs : BranchesHaveType θ Γⁱ cons bs τⁱ)
                                → (δs↓ : Acc _<_ (size-bs δs))
                                → μ-branches (branches-thinning↓ Γ⊂Γ' Γ'ok δs δs↓) ≡ CR.act-branches (ext-k' k suc) (μ-branches δs)
  μ-branches-thinning↓-commutes Γ⊂Γ' Γ'ok NoBranches (acc rec) = refl
  μ-branches-thinning↓-commutes Γ⊂Γ' Γ'ok (OneMoreBranch εδ δs) (acc rec) with Γ⊢ε⦂τ-⇒-Γok εδ | Γ⊢ε⦂τ-⇒-Γok-smaller εδ
  ... | TCTX-Bind _ conτδ
      | sub-≤
      rewrite μ-branches-thinning↓-commutes Γ⊂Γ' Γ'ok δs (rec _ (s≤s (₂≤₂ _ _)))
            = refl

μ-τ-thinning-commutes : {Γⁱ : I.Ctx (k + ℓ)}
                      → (Γ⊂Γ' : k by Γⁱ ⊂' Γⁱ')
                      → (Γ'ok : [ θ ] Γⁱ' ok)
                      → (τδ : [ θ ] Γⁱ ⊢ τⁱ)
                      → μ-τ (Γ⊢τ-thinning Γ⊂Γ' Γ'ok τδ) ≡ CR.act-ε (ext-k' k suc) (μ-τ τδ)
μ-τ-thinning-commutes Γ⊂Γ' Γ'ok τδ = μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok τδ (<-wellFounded _)

μ-τ-weakening-commutes : (Γok : [ θ ] Γⁱ ok)
                       → (τ'δ : [ θ ] Γⁱ ⊢ τⁱ')
                       → (τδ : [ θ ] Γⁱ ⊢ τⁱ)
                       → μ-τ (Γ⊢τ-weakening Γok τ'δ τδ) ≡ CR.weaken-ε (μ-τ τδ)
μ-τ-weakening-commutes Γok τ'δ = μ-τ-thinning-commutes ignore-head (TCTX-Bind Γok τ'δ)


μ-ε-thinning-commutes : {Γⁱ : I.Ctx (k + ℓ)}
                      → (Γ⊂Γ' : k by Γⁱ ⊂' Γⁱ')
                      → (Γ'ok : [ θ ] Γⁱ' ok)
                      → (εδ : [ θ ] Γⁱ ⊢ εⁱ ⦂ τⁱ)
                      → μ-ε (Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok εδ) ≡ CR.act-ε (ext-k' k suc) (μ-ε εδ)
μ-ε-thinning-commutes Γ⊂Γ' Γ'ok εδ = μ-ε-thinning↓-commutes Γ⊂Γ' Γ'ok εδ (<-wellFounded _)

μ-ε-weakening-commutes : (Γok : [ θ ] Γⁱ ok)
                       → (τ'δ : [ θ ] Γⁱ ⊢ τⁱ')
                       → (εδ : [ θ ] Γⁱ ⊢ εⁱ ⦂ τⁱ)
                       → μ-ε (Γ⊢ε⦂τ-weakening Γok τ'δ εδ) ≡ CR.weaken-ε (μ-ε εδ)
μ-ε-weakening-commutes Γok τ'δ = μ-ε-thinning-commutes ignore-head (TCTX-Bind Γok τ'δ)

μ-ε-weakening-suffix-commutes : {Δⁱ : CtxSuffix ℓ k}
                              → (Γ++Δok : [ θ ] (Γⁱ ++ Δⁱ) ok)
                              → (εδ : [ θ ] Γⁱ ⊢ εⁱ ⦂ τⁱ)
                              → μ-ε (Γ⊢ε⦂τ-weakening-suffix Γ++Δok εδ) ≡ CR.weaken-ε-k k (μ-ε εδ)
μ-ε-weakening-suffix-commutes {εⁱ = εⁱ} {τⁱ = τⁱ} {Δⁱ = ⊘} Γ++Δok εδ
  rewrite IR.act-ε-id (λ _ → refl) εⁱ
        | IR.act-τ-id (λ _ → refl) τⁱ
        = refl
μ-ε-weakening-suffix-commutes {k = suc k} {εⁱ = εⁱ} {τⁱ = τⁱ} {Δⁱ = Δⁱ , _} (TCTX-Bind Γ++Δok τδ) εδ
  rewrite sym (IR.act-ε-distr (raise k) suc εⁱ)
        | sym (IR.act-τ-distr (raise k) suc τⁱ)
        = trans
            (μ-ε-weakening-commutes Γ++Δok τδ (Γ⊢ε⦂τ-weakening-suffix Γ++Δok εδ))
            (cong CR.weaken-ε (μ-ε-weakening-suffix-commutes Γ++Δok εδ))
