{-# OPTIONS --safe #-}

module Surface.Theorems.Thinning where

open import Data.Fin.Base using (zero; suc; raise)
open import Data.Nat.Base
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Data.Vec.Base using (lookup; _∷_)
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
open import Surface.Operational.BetaEquivalence
open import Surface.Derivations
open import Surface.Theorems.Helpers

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
              → Γ' ok[ φ ]
              → Γ ⊢[ φ ] τ <: τ'
              → Γ' ⊢[ φ ] R.act-τ (ext-k' k suc) τ <: R.act-τ (ext-k' k suc) τ'
  <:-thinning Γ⊂Γ' Γ'ok (ST-Base oracle is-just) = ST-Base oracle (Oracle.thin oracle Γ⊂Γ' is-just)
  <:-thinning Γ⊂Γ' Γ'ok (ST-Arr <:₁δ <:₂δ omitted omitted) =
    let foo = {! !}
     in ST-Arr
          (<:-thinning Γ⊂Γ' Γ'ok <:₁δ)
          (<:-thinning (append-both Γ⊂Γ') (TCTX-Bind Γ'ok {! !}) <:₂δ)
          omitted
          omitted
  <:-thinning Γ⊂Γ' Γ'ok (ST-Arr <:₁δ <:₂δ (enriched ⇒δ) (enriched τ₁'δ)) =
    let τ₁'δ' = Γ⊢τ-thinning Γ⊂Γ' Γ'ok τ₁'δ
     in ST-Arr
          (<:-thinning Γ⊂Γ' Γ'ok <:₁δ)
          (<:-thinning (append-both Γ⊂Γ') (TCTX-Bind Γ'ok τ₁'δ') <:₂δ)
          (enriched (Γ⊢τ-thinning Γ⊂Γ' Γ'ok ⇒δ))
          (enriched τ₁'δ')

  Γ⊢τ-thinning : {Γ : Ctx (k + ℓ)}
               → (Γ⊂Γ' : k by Γ ⊂' Γ')
               → Γ' ok[ φ ]
               → Γ ⊢[ φ ] τ
               → Γ' ⊢[ φ ] R.act-τ (ext-k' k suc) τ
  Γ⊢τ-thinning Γ⊂Γ' Γ'ok (TWF-TrueRef _) = TWF-TrueRef Γ'ok
  Γ⊢τ-thinning Γ⊂Γ' Γ'ok (TWF-Base ε₁δ ε₂δ)
    = TWF-Base
        (Γ⊢ε⦂τ-thinning (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₁δ)
        (Γ⊢ε⦂τ-thinning (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₂δ)
  Γ⊢τ-thinning Γ⊂Γ' Γ'ok (TWF-Conj δ₁ δ₂) = TWF-Conj (Γ⊢τ-thinning Γ⊂Γ' Γ'ok δ₁) (Γ⊢τ-thinning Γ⊂Γ' Γ'ok δ₂)
  Γ⊢τ-thinning Γ⊂Γ' Γ'ok (TWF-Arr δ₁ δ₂)
    = TWF-Arr
        (Γ⊢τ-thinning Γ⊂Γ' Γ'ok δ₁)
        (Γ⊢τ-thinning (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (Γ⊢τ-thinning Γ⊂Γ' Γ'ok δ₁)) δ₂)
  Γ⊢τ-thinning {k = k} {ℓ = ℓ} {Γ' = Γ'} {φ = φ} {Γ = Γ} Γ⊂Γ' Γ'ok (TWF-ADT consδs) = TWF-ADT (thin-cons consδs)
    where
    thin-cons : {cons : ADTCons nₐ (k + ℓ)}
              → All (Γ ⊢[ φ ]_) cons
              → All (Γ' ⊢[ φ ]_) (R.act-cons (ext-k' k suc) cons)
    thin-cons [] = []
    thin-cons (δ ∷ consδs) = Γ⊢τ-thinning Γ⊂Γ' Γ'ok δ ∷ thin-cons consδs

  Γ⊢ε⦂τ-thinning : {Γ : Ctx (k + ℓ)}
                 → (Γ⊂Γ' : k by Γ ⊂' Γ')
                 → Γ' ok[ φ ]
                 → Γ ⊢[ φ ] ε ⦂ τ
                 → Γ' ⊢[ φ ] R.act-ε (ext-k' k suc) ε ⦂ R.act-τ (ext-k' k suc) τ
  Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok (T-Unit _) = T-Unit Γ'ok
  Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok (T-Var Γok ∈) = T-Var Γ'ok (∈-thinning Γ⊂Γ' ∈)
  Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok (T-Abs arrδ@(TWF-Arr domδ codδ) δ)
    = T-Abs
        (Γ⊢τ-thinning Γ⊂Γ' Γ'ok arrδ)
        (Γ⊢ε⦂τ-thinning (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (Γ⊢τ-thinning Γ⊂Γ' Γ'ok domδ)) δ)
  Γ⊢ε⦂τ-thinning {k = k} Γ⊂Γ' Γ'ok (T-App {τ₂ = τ₂} {ε₂ = ε₂} δ₁ δ₂)
    rewrite ρ-subst-distr-τ-0 (ext-k' k suc) ε₂ τ₂
          | R.act-τ-extensionality (ρ-0th-is-ext (ext-k' k suc)) τ₂
          = T-App (Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok δ₁) (Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok δ₂)
  Γ⊢ε⦂τ-thinning {k = k} {ℓ = ℓ} {Γ' = Γ'} {Γ = Γ} Γ⊂Γ' Γ'ok (T-Case resδ δ branchesδ)
    = T-Case
        (Γ⊢τ-thinning Γ⊂Γ' Γ'ok resδ)
        (Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok δ)
        (thin-branches branchesδ)
    where
    thin-branches : {cons : ADTCons nₐ (k + ℓ)}
                  → {bs : CaseBranches nₐ (k + ℓ)}
                  → BranchesHaveType φ Γ cons bs τ
                  → BranchesHaveType φ Γ' (R.act-cons (ext-k' k suc) cons) (R.act-branches (ext-k' k suc) bs) (R.act-τ (ext-k' k suc) τ)
    thin-branches NoBranches = NoBranches
    thin-branches {φ = φ} {τ = τ} (OneMoreBranch {ε' = ε'} {conτ = conτ} εδ branchesδ) =
      let conτδ' = Γ⊢τ-thinning Γ⊂Γ' Γ'ok {! conτδ !}
          εδ' = Γ⊢ε⦂τ-thinning (append-both Γ⊂Γ') (TCTX-Bind Γ'ok conτδ') {! εδ !}
          derivable τ = Γ' , R.act-τ (ext-k' k suc) conτ ⊢[ φ ] R.act-ε (R.ext (ext-k' k suc)) ε' ⦂ τ
          εδ'-substed = subst derivable (ext-k'-suc-commute k τ) {! εδ' !}
       in OneMoreBranch
            εδ'-substed
            (thin-branches branchesδ)
  Γ⊢ε⦂τ-thinning {k = k} {φ = φ} Γ⊂Γ' Γ'ok (T-Con {ε = ε} {ι = ι} {cons = cons} refl δ adtτ) =
    let δ' = Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok δ
        δ-substed = subst (λ τ → _ ⊢[ φ ] R.act-ε (ext-k' k suc) ε ⦂ τ) (R.cons-lookup-comm (ext-k' k suc) ι cons) δ'
     in T-Con
          refl
          δ-substed
          (Γ⊢τ-thinning Γ⊂Γ' Γ'ok adtτ)
  Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok (T-Sub δ τ'δ <:)
    = T-Sub
        (Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok δ)
        (Γ⊢τ-thinning Γ⊂Γ' Γ'ok τ'δ)
        (<:-thinning Γ⊂Γ' Γ'ok <:)
  Γ⊢ε⦂τ-thinning {k = k} Γ⊂Γ' Γ'ok (T-RConv δ τ'δ τ~τ')
    = T-RConv
        (Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok δ)
        (Γ⊢τ-thinning Γ⊂Γ' Γ'ok τ'δ)
        (ρ-preserves-↭βτ (ext-k' k suc) τ~τ')

<:-weakening : Γ ok[ φ ]
             → Γ ⊢[ φ ] τ'
             → Γ ⊢[ φ ] τ₁ <: τ₂
             → (Γ , τ') ⊢[ φ ] R.weaken-τ τ₁ <: R.weaken-τ τ₂
<:-weakening Γok Γ⊢τ' = <:-thinning ignore-head (TCTX-Bind Γok Γ⊢τ')

Γ⊢τ-weakening : Γ ok[ φ ]
              → Γ ⊢[ φ ] τ'
              → Γ ⊢[ φ ] τ
              → (Γ , τ') ⊢[ φ ] R.weaken-τ τ
Γ⊢τ-weakening Γok Γ⊢τ' = Γ⊢τ-thinning ignore-head (TCTX-Bind Γok Γ⊢τ')

Γ⊢ε⦂τ-weakening : Γ ok[ φ ]
                → Γ ⊢[ φ ] τ'
                → Γ ⊢[ φ ] ε ⦂ τ
                → (Γ , τ') ⊢[ φ ] R.weaken-ε ε ⦂ R.weaken-τ τ
Γ⊢ε⦂τ-weakening Γok Γ⊢τ' = Γ⊢ε⦂τ-thinning ignore-head (TCTX-Bind Γok Γ⊢τ')

Γ⊢ε⦂τ-weakening-suffix : {Δ : CtxSuffix ℓ k}
                       → (Γ ++ Δ) ok[ φ ]
                       → Γ ⊢[ φ ] ε ⦂ τ
                       → Γ ++ Δ ⊢[ φ ] R.weaken-ε-k k ε ⦂ R.weaken-τ-k k τ
Γ⊢ε⦂τ-weakening-suffix {ε = ε} {τ = τ} {Δ = ⊘} Γ++Δok εδ
  rewrite R.act-ε-id (λ _ → refl) ε
        | R.act-τ-id (λ _ → refl) τ
        = εδ
Γ⊢ε⦂τ-weakening-suffix {k = suc k} {ε = ε} {τ = τ} {Δ = Δ , _} (TCTX-Bind Γ++Δok τδ) εδ
  rewrite sym (R.act-ε-distr (raise k) suc ε)
        | sym (R.act-τ-distr (raise k) suc τ)
        = Γ⊢ε⦂τ-weakening Γ++Δok τδ (Γ⊢ε⦂τ-weakening-suffix Γ++Δok εδ)
