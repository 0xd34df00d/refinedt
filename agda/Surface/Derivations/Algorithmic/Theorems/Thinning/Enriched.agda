{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Thinning.Enriched where

open import Data.Fin using (zero; suc; raise; #_)
open import Data.Nat.Base
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Data.Vec.Base using (lookup; _∷_; [])
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import Common.Helpers
open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Subcontext
open import Surface.Syntax.Membership
open import Surface.Syntax.Renaming as R
open import Surface.Syntax.Substitution as S
open import Surface.Syntax.Substitution.Distributivity
open import Surface.Derivations.Algorithmic

∈-thinning : {Γ : Ctx (k + ℓ)}
           → k by Γ ⊂' Γ'
           → τ ∈ Γ at ι
           → R.act-τ (ext-k' k suc) τ ∈ Γ' at ext-k' k suc ι
∈-thinning ignore-head ∈ = ∈-suc refl ∈
∈-thinning (append-both {k = k} {τ = τ} Γ⊂Γ') (∈-zero refl) = ∈-zero (ext-k'-suc-commute k τ)
∈-thinning (append-both {k = k} Γ⊂Γ') (∈-suc {τ = τ} refl ∈) = ∈-suc (ext-k'-suc-commute k τ) (∈-thinning Γ⊂Γ' ∈)

mutual
  <:-thinning : {Γ : Ctx (k + ℓ)}
              → (Γ⊂Γ' : k by Γ ⊂' Γ')
              → Γ' ok[ θ , E ]
              → (δ : Γ ⊢[ θ , E ] τ' <: τ)
              → Γ' ⊢[ θ , E ] R.act-τ (ext-k' k suc) τ' <: R.act-τ (ext-k' k suc) τ
  <:-thinning {θ = θ} Γ⊂Γ' Γ'ok (ST-Base is-just ⦃ enriched ρ₁δ ⦄ ⦃ enriched ρ₂δ ⦄)
    = ST-Base
        (Oracle.thin θ Γ⊂Γ' is-just)
        ⦃ enriched (Γ⊢τ-thinning Γ⊂Γ' Γ'ok ρ₁δ) ⦄
        ⦃ enriched (Γ⊢τ-thinning Γ⊂Γ' Γ'ok ρ₂δ) ⦄
  <:-thinning Γ⊂Γ' Γ'ok (ST-Arr <:₁δ <:₂δ ⦃ enriched τ₁⇒τ₂'δ ⦄ ⦃ enriched τ₁'⇒τ₂δ@(TWF-Arr τ₁'δ _) ⦄)
    = let τ₁'δ' = Γ⊢τ-thinning Γ⊂Γ' Γ'ok τ₁'δ
       in ST-Arr
            (<:-thinning Γ⊂Γ' Γ'ok <:₁δ)
            (<:-thinning (append-both Γ⊂Γ') (TCTX-Bind Γ'ok τ₁'δ') <:₂δ)
            ⦃ enriched (Γ⊢τ-thinning Γ⊂Γ' Γ'ok τ₁⇒τ₂'δ) ⦄
            ⦃ enriched (Γ⊢τ-thinning Γ⊂Γ' Γ'ok τ₁'⇒τ₂δ) ⦄
  <:-thinning {k = k} {ℓ = ℓ} Γ⊂Γ' Γ'ok (ST-ADT cons-<:) = ST-ADT (go cons-<:)
    where
    go : {cons' cons : ADTCons nₐ (k + ℓ)}
       → AllSubtypes _ _ E cons' cons
       → AllSubtypes _ _ E (R.act-cons (ext-k' k suc) cons') (R.act-cons (ext-k' k suc) cons)
    go {cons' = []}    {[]}    []             = []
    go {cons' = _ ∷ _} {_ ∷ _} (τδ ∷ cons-<:) = <:-thinning Γ⊂Γ' Γ'ok τδ ∷ go cons-<:

  Γ⊢τ-thinning : {Γ : Ctx (k + ℓ)}
               → (Γ⊂Γ' : k by Γ ⊂' Γ')
               → Γ' ok[ θ , E ]
               → (τδ : Γ ⊢[ θ , E ] τ)
               → Γ' ⊢[ θ , E ] R.act-τ (ext-k' k suc) τ
  Γ⊢τ-thinning Γ⊂Γ' Γ'ok (TWF-TrueRef Γok) = TWF-TrueRef Γ'ok
  Γ⊢τ-thinning Γ⊂Γ' Γ'ok (TWF-Base ε₁δ ε₂δ)
    = TWF-Base
        (Γ⊢ε⦂τ-thinning (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₁δ)
        (Γ⊢ε⦂τ-thinning (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₂δ)
  Γ⊢τ-thinning Γ⊂Γ' Γ'ok (TWF-Conj τ₁δ τ₂δ) = TWF-Conj (Γ⊢τ-thinning Γ⊂Γ' Γ'ok τ₁δ) (Γ⊢τ-thinning Γ⊂Γ' Γ'ok τ₂δ)
  Γ⊢τ-thinning Γ⊂Γ' Γ'ok (TWF-Arr τ₁δ τ₂δ)
    = let τ₁δ' = Γ⊢τ-thinning Γ⊂Γ' Γ'ok τ₁δ
       in TWF-Arr τ₁δ' (Γ⊢τ-thinning (append-both Γ⊂Γ') (TCTX-Bind Γ'ok τ₁δ') τ₂δ)
  Γ⊢τ-thinning Γ⊂Γ' Γ'ok (TWF-ADT consδs) = TWF-ADT (cons-thinning Γ⊂Γ' Γ'ok consδs)

  cons-thinning : {Γ : Ctx (k + ℓ)}
                → {cons : ADTCons nₐ (k + ℓ)}
                → (Γ⊂Γ' : k by Γ ⊂' Γ')
                → Γ' ok[ θ , E ]
                → (consδs : All (Γ ⊢[ θ , E ]_) cons)
                → All (Γ' ⊢[ θ , E ]_) (R.act-cons (ext-k' k suc) cons)
  cons-thinning Γ⊂Γ' Γ'ok [] = []
  cons-thinning Γ⊂Γ' Γ'ok (τδ ∷ consδs) = Γ⊢τ-thinning Γ⊂Γ' Γ'ok τδ ∷ cons-thinning Γ⊂Γ' Γ'ok consδs

  branches-thinning : {Γ : Ctx (k + ℓ)}
                    → {cons : ADTCons nₐ (k + ℓ)}
                    → {bs : CaseBranches nₐ (k + ℓ)}
                    → (Γ⊂Γ' : k by Γ ⊂' Γ')
                    → Γ' ok[ θ , E ]
                    → (consδs : All (Γ ⊢[ θ , E ]_) cons)
                    → (bsδ : BranchesHaveType θ E Γ cons bs τ)
                    → BranchesHaveType θ E Γ' (R.act-cons (ext-k' k suc) cons) (R.act-branches (ext-k' k suc) bs) (R.act-τ (ext-k' k suc) τ)
  branches-thinning Γ⊂Γ' Γ'ok _ NoBranches = NoBranches
  branches-thinning {k = k} Γ⊂Γ' Γ'ok (consδ ∷ consδs) (OneMoreBranch εδ bsδ)
    = let consδ' = Γ⊢τ-thinning Γ⊂Γ' Γ'ok consδ
          εδ' = Γ⊢ε⦂τ-thinning (append-both Γ⊂Γ') (TCTX-Bind Γ'ok consδ') εδ
          εδ' = subst (_ ⊢[ _ , _ of _ ] _ ⦂_) (ext-k'-suc-commute k _) εδ'
       in OneMoreBranch
            εδ'
            (branches-thinning Γ⊂Γ' Γ'ok consδs bsδ)

  Γ⊢ε⦂τ-thinning : {Γ : Ctx (k + ℓ)}
                 → (Γ⊂Γ' : k by Γ ⊂' Γ')
                 → Γ' ok[ θ , E ]
                 → (εδ : Γ ⊢[ θ , E of κ ] ε ⦂ τ)
                 → Γ' ⊢[ θ , E of κ ] R.act-ε (ext-k' k suc) ε ⦂ R.act-τ (ext-k' k suc) τ
  Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok (T-Unit Γok ⦃ enriched τδ ⦄) = T-Unit Γ'ok ⦃ enriched (Γ⊢τ-thinning Γ⊂Γ' Γ'ok τδ) ⦄
  Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok (T-Var Γok ∈ ⦃ enriched τδ ⦄) =  T-Var Γ'ok (∈-thinning Γ⊂Γ' ∈) ⦃ enriched (Γ⊢τ-thinning Γ⊂Γ' Γ'ok τδ) ⦄
  Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok (T-Abs εδ ⦃ enriched τ₁⇒τ₂δ@(TWF-Arr τ₁δ _) ⦄)
    = T-Abs (Γ⊢ε⦂τ-thinning (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (Γ⊢τ-thinning Γ⊂Γ' Γ'ok τ₁δ)) εδ) ⦃ enriched (Γ⊢τ-thinning Γ⊂Γ' Γ'ok τ₁⇒τ₂δ) ⦄
  Γ⊢ε⦂τ-thinning {k = k} Γ⊂Γ' Γ'ok (T-App ε₁δ ε₂δ refl ⦃ enriched τδ ⦄)
    = T-App
        (Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok ε₁δ)
        (Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok ε₂δ)
        (ρ-subst-distr-τ-0 (ext-k' k suc) _ _)
        ⦃ enriched (Γ⊢τ-thinning Γ⊂Γ' Γ'ok τδ) ⦄
  Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok (T-Case resδ εδ@(T-Sub _ _ ⦃ enriched (TWF-ADT consδs) ⦄) bsδ)
    = T-Case
        (Γ⊢τ-thinning Γ⊂Γ' Γ'ok resδ)
        (Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok εδ)
        (branches-thinning Γ⊂Γ' Γ'ok consδs bsδ)
  Γ⊢ε⦂τ-thinning {k = k} Γ⊂Γ' Γ'ok (T-Con {ι = ι} {cons = cons} <:δ εδ adtτ)
    = let lookup-comm = R.cons-lookup-comm (ext-k' k suc) ι cons
          <:δ' = <:-thinning Γ⊂Γ' Γ'ok <:δ
       in T-Con
            (subst (_ ⊢[ _ , _ ] _ <:_) lookup-comm <:δ')
            (Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok εδ)
            (Γ⊢τ-thinning Γ⊂Γ' Γ'ok adtτ)
  Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok (T-Sub εδ <:δ ⦃ enriched τδ ⦄)
    = T-Sub
        (Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok εδ)
        (<:-thinning Γ⊂Γ' Γ'ok <:δ)
        ⦃ enriched (Γ⊢τ-thinning Γ⊂Γ' Γ'ok τδ) ⦄

<:-weakening : Γ ok[ θ , E ]
             → Γ ⊢[ θ , E ] τ'
             → Γ ⊢[ θ , E ] τ₁ <: τ₂
             → (Γ , τ') ⊢[ θ , E ] R.weaken-τ τ₁ <: R.weaken-τ τ₂
<:-weakening Γok Γ⊢τ' = <:-thinning ignore-head (TCTX-Bind Γok Γ⊢τ')

Γ⊢τ-weakening : Γ ok[ θ , E ]
              → Γ ⊢[ θ , E ] τ'
              → Γ ⊢[ θ , E ] τ
              → (Γ , τ') ⊢[ θ , E ] R.weaken-τ τ
Γ⊢τ-weakening Γok Γ⊢τ' = Γ⊢τ-thinning ignore-head (TCTX-Bind Γok Γ⊢τ')

Γ⊢ε⦂τ-weakening : Γ ok[ θ , E ]
                → Γ ⊢[ θ , E ] τ'
                → Γ ⊢[ θ , E of κ ] ε ⦂ τ
                → (Γ , τ') ⊢[ θ , E of κ ] R.weaken-ε ε ⦂ R.weaken-τ τ
Γ⊢ε⦂τ-weakening Γok Γ⊢τ' = Γ⊢ε⦂τ-thinning ignore-head (TCTX-Bind Γok Γ⊢τ')

Γ⊢ε⦂τ-weakening-suffix : {Δ : CtxSuffix ℓ k}
                       → (Γ ++ Δ) ok[ θ , E ]
                       → Γ ⊢[ θ , E of κ ] ε ⦂ τ
                       → Γ ++ Δ ⊢[ θ , E of κ ] R.weaken-ε-k k ε ⦂ R.weaken-τ-k k τ
Γ⊢ε⦂τ-weakening-suffix {ε = ε} {τ = τ} {Δ = ⊘} Γ++Δok εδ
  rewrite R.act-ε-id (λ _ → refl) ε
        | R.act-τ-id (λ _ → refl) τ
        = εδ
Γ⊢ε⦂τ-weakening-suffix {k = suc k} {ε = ε} {τ = τ} {Δ = Δ , _} (TCTX-Bind Γ++Δok τδ) εδ
  rewrite sym (R.act-ε-distr (raise k) suc ε)
        | sym (R.act-τ-distr (raise k) suc τ)
        = Γ⊢ε⦂τ-weakening Γ++Δok τδ (Γ⊢ε⦂τ-weakening-suffix Γ++Δok εδ)
