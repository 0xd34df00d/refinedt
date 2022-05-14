{-# OPTIONS --safe #-}

module Intermediate.Derivations.Algorithmic.Theorems.Thinning where

open import Data.Fin using (zero; suc; raise; #_)
open import Data.Nat.Base
open import Data.Nat.Induction
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; ≤-stepsˡ)
open import Data.Vec.Base using (lookup; _∷_; [])
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import Common.Helpers
open import Intermediate.Syntax
open import Intermediate.Syntax.CtxSuffix
open import Intermediate.Syntax.Subcontext
open import Intermediate.Syntax.Membership
open import Intermediate.Syntax.Renaming as R
open import Intermediate.Syntax.Substitution as S
open import Intermediate.Syntax.Substitution.Distributivity
open import Intermediate.Derivations.Algorithmic
open import Intermediate.Derivations.Algorithmic.Theorems.Helpers
open import Intermediate.Derivations.Algorithmic.Theorems.Agreement.Γok
open import Intermediate.Derivations.Algorithmic.Theorems.Agreement.Γok.WF

∈-thinning : {Γ : Ctx (k + ℓ)}
           → k by Γ ⊂' Γ'
           → τ ∈ Γ at ι
           → R.act-τ (ext-k' k suc) τ ∈ Γ' at ext-k' k suc ι
∈-thinning ignore-head ∈ = ∈-suc refl ∈
∈-thinning (append-both {k = k} {τ = τ} Γ⊂Γ') (∈-zero refl) = ∈-zero (ext-k'-suc-commute k τ)
∈-thinning (append-both {k = k} Γ⊂Γ') (∈-suc {τ = τ} refl ∈) = ∈-suc (ext-k'-suc-commute k τ) (∈-thinning Γ⊂Γ' ∈)

mutual
  <:-thinning↓ : {Γ : Ctx (k + ℓ)}
               → (Γ⊂Γ' : k by Γ ⊂' Γ')
               → [ θ ] Γ' ok
               → (δ : [ θ ] Γ ⊢ τ <: τ')
               → Acc _<_ (size-<: δ)
               → [ θ ] Γ' ⊢ R.act-τ (ext-k' k suc) τ <: R.act-τ (ext-k' k suc) τ'
  <:-thinning↓ {θ = θ} Γ⊂Γ' Γ'ok (ST-Base is-just ρ₁δ ρ₂δ) (acc rec) =
    ST-Base
      (Oracle.thin θ Γ⊂Γ' is-just)
      (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok ρ₁δ (rec _ (s≤s (₁≤₂ _ _))))
      (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok ρ₂δ (rec _ (s≤s (₂≤₂ _ _))))
  <:-thinning↓ Γ⊂Γ' Γ'ok arr@(ST-Arr <:₁δ <:₂δ τ₁⇒τ₂'δ τ₁'⇒τ₂δ) (acc rec)
    with τ₁'⇒τ₂δ'@(TWF-Arr τ₁'δ' _) ← Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok τ₁'⇒τ₂δ (rec _ (<₄ (ST-Arr-size-vec arr) (# 3)))
       = let rec-args = ST-Arr-size-vec arr
          in ST-Arr
              (<:-thinning↓ Γ⊂Γ' Γ'ok <:₁δ (rec _ (<₄ rec-args (# 0))))
              (<:-thinning↓ (append-both Γ⊂Γ') (TCTX-Bind Γ'ok τ₁'δ') <:₂δ (rec _ (<₄ rec-args (# 1))))
              (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok τ₁⇒τ₂'δ (rec _ (<₄ rec-args (# 2))))
              τ₁'⇒τ₂δ'

  Γ⊢τ-thinning↓ : {Γ : Ctx (k + ℓ)}
                → (Γ⊂Γ' : k by Γ ⊂' Γ')
                → [ θ ] Γ' ok
                → (δ : [ θ ] Γ ⊢ τ)
                → Acc _<_ (size-twf δ)
                → [ θ ] Γ' ⊢ R.act-τ (ext-k' k suc) τ
  Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok (TWF-TrueRef _) _ = TWF-TrueRef Γ'ok
  Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok (TWF-Base ε₁δ ε₂δ) (acc rec) =
    let acc₁ = rec _ (s≤s (₁≤₂ _ _))
        acc₂ = rec _ (s≤s (₂≤₂ _ _))
     in TWF-Base
          (Γ⊢ε⦂τ-thinning↓ (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₁δ acc₁)
          (Γ⊢ε⦂τ-thinning↓ (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₂δ acc₂)
  Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok (TWF-Conj δ₁ δ₂) (acc rec) =
    let acc₁ = rec _ (s≤s (₁≤₂ _ _))
        acc₂ = rec _ (s≤s (₂≤₂ _ _))
     in TWF-Conj (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok δ₁ acc₁) (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok δ₂ acc₂)
  Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok (TWF-Arr δ₁ δ₂) (acc rec) =
    let acc₁ = rec _ (s≤s (₁≤₂ _ _))
        acc₂ = rec _ (s≤s (₂≤₂ _ _))
     in TWF-Arr
          (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok δ₁ acc₁)
          (Γ⊢τ-thinning↓ (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok δ₁ acc₁)) δ₂ acc₂)
  Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok (TWF-ADT consδs) (acc rec) = TWF-ADT (cons-thinning↓ Γ⊂Γ' Γ'ok consδs (rec _ ≤-refl))

  Γ⊢ε⦂τ-thinning↓ : {Γ : Ctx (k + ℓ)}
                  → (Γ⊂Γ' : k by Γ ⊂' Γ')
                  → [ θ ] Γ' ok
                  → (δ : [ θ ] Γ ⊢ ε ⦂ τ)
                  → Acc _<_ (size-t δ)
                  → [ θ ] Γ' ⊢ R.act-ε (ext-k' k suc) ε ⦂ R.act-τ (ext-k' k suc) τ
  Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok (T-Unit _) _ = T-Unit Γ'ok
  Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok (T-Var Γok ∈) _ = T-Var Γ'ok (∈-thinning Γ⊂Γ' ∈)
  Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok (T-Abs arrδ@(TWF-Arr domδ codδ) δ) (acc rec) =
    let acc₁ = rec _ (s≤s (₁≤₂ _ (size-t δ)))
        acc₂ = rec _ (s≤s (≤-trans (≤-trans (₁≤₂ _ (size-twf codδ)) (n≤1+n _)) (₁≤₂ _ (size-t δ))))
        acc₃ = rec _ (s≤s (₂≤₂ _ _))
     in T-Abs
          (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok arrδ acc₁)
          (Γ⊢ε⦂τ-thinning↓ (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok domδ acc₂)) δ acc₃)
  Γ⊢ε⦂τ-thinning↓ {k = k} Γ⊂Γ' Γ'ok (T-App {τ₂ = τ₂} {ε₂ = ε₂} δ₁ δ₂ refl resτδ) (acc rec)
    rewrite ρ-subst-distr-τ-0 (ext-k' k suc) ε₂ τ₂
          = let acc₁ = rec _ (s≤s (₁≤₂ _ _))
                acc₂ = rec _ (s≤s (₂≤₃ (size-t δ₁) _ _))
                acc₃ = rec _ (s≤s (₃≤₃ (size-t δ₁) (size-t δ₂) _))
                resτδ' = Γ⊢τ-thinning↓  Γ⊂Γ' Γ'ok resτδ acc₃
                resτδ' = subst ([ _ ] _ ⊢_) (ρ-subst-distr-τ-0 (ext-k' k suc) ε₂ τ₂) resτδ'
             in T-App
                  (Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok δ₁ acc₁)
                  (Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok δ₂ acc₂)
                  refl
                  resτδ'
  Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok (T-Case resδ δ branchesδ) (acc rec) =
    let acc₁ = rec _ (s≤s (₂≤₃ (size-t δ) (size-twf resδ) (size-bs branchesδ)))
        acc₂ = rec _ (s≤s (₁≤₂ _ _))
        acc₃ = rec _ (s≤s (₃≤₃ (size-t δ) (size-twf resδ) (size-bs branchesδ)))
     in T-Case
          (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok resδ acc₁)
          (Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok δ acc₂)
          (branches-thinning↓ Γ⊂Γ' Γ'ok branchesδ acc₃)
  Γ⊢ε⦂τ-thinning↓ {k = k} {θ = θ} Γ⊂Γ' Γ'ok (T-Con {ε = ε} {ι = ι} {cons = cons} refl δ (TWF-ADT consδs)) (acc rec) =
    let acc₁ = rec _ (s≤s (₁≤₂ _ _))
        acc₂ = rec _ (s≤s (₂≤₂ _ _))
        δ' = Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok δ acc₁
        δ-substed = subst (λ τ → [ θ ] _ ⊢ R.act-ε (ext-k' k suc) ε ⦂ τ) (R.cons-lookup-comm (ext-k' k suc) ι cons) δ'
     in T-Con
          refl
          δ-substed
          (TWF-ADT (cons-thinning↓ Γ⊂Γ' Γ'ok consδs acc₂))
  Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok (T-SubW <: εδ) (acc rec) =
    let acc₁ = rec _ (s≤s (₂≤₂ _ _))
        acc₂ = rec _ (s≤s (₁≤₂ _ _))
     in T-SubW
          (<:-thinning↓ Γ⊂Γ' Γ'ok <: acc₁)
          (Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok εδ acc₂)

  cons-thinning↓ : {Γ : Ctx (k + ℓ)}
                 → {cons : ADTCons nₐ (k + ℓ)}
                 → (Γ⊂Γ' : k by Γ ⊂' Γ')
                 → [ θ ] Γ' ok
                 → (δs : All ([ θ ] Γ ⊢_) cons)
                 → Acc _<_ (size-all-cons δs)
                 → All ([ θ ] Γ' ⊢_) (R.act-cons (ext-k' k suc) cons)
  cons-thinning↓ Γ⊂Γ' Γ'ok [] _ = []
  cons-thinning↓ Γ⊂Γ' Γ'ok (δ ∷ consδs) (acc rec) =
    let acc₁ = rec _ (s≤s (₁≤₂ _ _))
        acc₂ = rec _ (s≤s (₂≤₂ _ _))
     in Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok δ acc₁ ∷ cons-thinning↓ Γ⊂Γ' Γ'ok consδs acc₂

  branches-thinning↓ : {Γ : Ctx (k + ℓ)}
                     → {cons : ADTCons nₐ (k + ℓ)}
                     → {bs : CaseBranches nₐ (k + ℓ)}
                     → (Γ⊂Γ' : k by Γ ⊂' Γ')
                     → [ θ ] Γ' ok
                     → (δs : BranchesHaveType θ Γ cons bs τ)
                     → Acc _<_ (size-bs δs)
                     → BranchesHaveType θ Γ' (R.act-cons (ext-k' k suc) cons) (R.act-branches (ext-k' k suc) bs) (R.act-τ (ext-k' k suc) τ)
  branches-thinning↓ Γ⊂Γ' Γ'ok NoBranches _ = NoBranches
  branches-thinning↓ {k = k} {Γ' = Γ'} {τ = τ} Γ⊂Γ' Γ'ok (OneMoreBranch {ε' = ε'} {conτ = conτ} εδ branchesδ) (acc rec) with Γ⊢ε⦂τ-⇒-Γok εδ | Γ⊢ε⦂τ-⇒-Γok-smaller εδ
  ... | TCTX-Bind _ conτδ | sub-≤ =
    let acc₁ = rec _ (s≤s (₁≤₂ _ _))
        acc₂ = rec _ (s≤s (₂≤₂ _ _))
        acc₃ = rec _ (s≤s (≤-trans (≤-trans (≤-stepsˡ 2 (₂≤₂ _ _)) sub-≤) (₁≤₂ _ _)))
        conτδ-thinned = Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok conτδ acc₃
        εδ' = Γ⊢ε⦂τ-thinning↓ (append-both Γ⊂Γ') (TCTX-Bind Γ'ok conτδ-thinned) εδ acc₁
        derivable τ = [ _ ] Γ' , R.act-τ (ext-k' k suc) conτ ⊢ R.act-ε (R.ext (ext-k' k suc)) ε' ⦂ τ
        εδ'-substed = subst derivable (ext-k'-suc-commute k τ) εδ'
     in OneMoreBranch
          εδ'-substed
          (branches-thinning↓ Γ⊂Γ' Γ'ok branchesδ acc₂)


<:-thinning : {Γ : Ctx (k + ℓ)}
            → (Γ⊂Γ' : k by Γ ⊂' Γ')
            → [ θ ] Γ' ok
            → [ θ ] Γ ⊢ τ <: τ'
            → [ θ ] Γ' ⊢ R.act-τ (ext-k' k suc) τ <: R.act-τ (ext-k' k suc) τ'
<:-thinning Γ⊂Γ' [Γ'ok] δ = <:-thinning↓ Γ⊂Γ' [Γ'ok] δ (<-wellFounded _)

Γ⊢τ-thinning : {Γ : Ctx (k + ℓ)}
             → (Γ⊂Γ' : k by Γ ⊂' Γ')
             → [ θ ] Γ' ok
             → [ θ ] Γ ⊢ τ
             → [ θ ] Γ' ⊢ R.act-τ (ext-k' k suc) τ
Γ⊢τ-thinning Γ⊂Γ' [Γ'ok] δ = Γ⊢τ-thinning↓ Γ⊂Γ' [Γ'ok] δ (<-wellFounded _)

Γ⊢ε⦂τ-thinning : {Γ : Ctx (k + ℓ)}
               → (Γ⊂Γ' : k by Γ ⊂' Γ')
               → [ θ ] Γ' ok
               → [ θ ] Γ ⊢ ε ⦂ τ
               → [ θ ] Γ' ⊢ R.act-ε (ext-k' k suc) ε ⦂ R.act-τ (ext-k' k suc) τ
Γ⊢ε⦂τ-thinning Γ⊂Γ' [Γ'ok] δ = Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' [Γ'ok] δ (<-wellFounded _)

<:-weakening : [ θ ] Γ ok
             → [ θ ] Γ ⊢ τ'
             → [ θ ] Γ ⊢ τ₁ <: τ₂
             → [ θ ] (Γ , τ') ⊢ R.weaken-τ τ₁ <: R.weaken-τ τ₂
<:-weakening Γok Γ⊢τ' = <:-thinning ignore-head (TCTX-Bind Γok Γ⊢τ')

Γ⊢τ-weakening : [ θ ] Γ ok
              → [ θ ] Γ ⊢ τ'
              → [ θ ] Γ ⊢ τ
              → [ θ ] (Γ , τ') ⊢ R.weaken-τ τ
Γ⊢τ-weakening Γok Γ⊢τ' = Γ⊢τ-thinning ignore-head (TCTX-Bind Γok Γ⊢τ')

Γ⊢ε⦂τ-weakening : [ θ ] Γ ok
                → [ θ ] Γ ⊢ τ'
                → [ θ ] Γ ⊢ ε ⦂ τ
                → [ θ ] (Γ , τ') ⊢ R.weaken-ε ε ⦂ R.weaken-τ τ
Γ⊢ε⦂τ-weakening Γok Γ⊢τ' = Γ⊢ε⦂τ-thinning ignore-head (TCTX-Bind Γok Γ⊢τ')

Γ⊢ε⦂τ-weakening-suffix : {Δ : CtxSuffix ℓ k}
                       → [ θ ] (Γ ++ Δ) ok
                       → [ θ ] Γ ⊢ ε ⦂ τ
                       → [ θ ] Γ ++ Δ ⊢ R.weaken-ε-k k ε ⦂ R.weaken-τ-k k τ
Γ⊢ε⦂τ-weakening-suffix {ε = ε} {τ = τ} {Δ = ⊘} Γ++Δok εδ
  rewrite R.act-ε-id (λ _ → refl) ε
        | R.act-τ-id (λ _ → refl) τ
        = εδ
Γ⊢ε⦂τ-weakening-suffix {k = suc k} {ε = ε} {τ = τ} {Δ = Δ , _} (TCTX-Bind Γ++Δok τδ) εδ
  rewrite sym (R.act-ε-distr (raise k) suc ε)
        | sym (R.act-τ-distr (raise k) suc τ)
        = Γ⊢ε⦂τ-weakening Γ++Δok τδ (Γ⊢ε⦂τ-weakening-suffix Γ++Δok εδ)
