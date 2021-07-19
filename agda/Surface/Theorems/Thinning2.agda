module Surface.Theorems.Thinning2 where

open import Data.Fin.Base using (zero; suc; raise)
open import Data.Nat.Base
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Data.Vec.Base using (lookup; _∷_)
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Common.Helpers
open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Membership hiding (_⊂'_; ignore-head; append-both)
open import Surface.Syntax.Renaming as R
open import Surface.Syntax.Substitution as S
open import Surface.Syntax.Substitution.Distributivity
open import Surface.Operational.BetaEquivalence
open import Surface.Derivations
open import Surface.Theorems.Agreement.Γok
open import Surface.Theorems.Agreement.Γok.WF
open import Surface.Theorems.Helpers

-- This has a slightly different (and less generic) type
-- than the ext-k version from the Actions module,
-- so it normalizes slightly differently
-- and is more convenient in the context of this module.
ext-k' : (k : ℕ)
       → (ρ : Fin ℓ → Fin (suc ℓ))
       → Fin (k + ℓ) → Fin (suc (k + ℓ))
ext-k' zero ρ = ρ
ext-k' (suc k) ρ = R.ext (ext-k' k ρ)

infix 4 _by_⊂'_
data _by_⊂'_ : (k : ℕ) → Ctx (k + ℓ) → Ctx (suc (k + ℓ)) → Set where
  ignore-head : zero by Γ ⊂' Γ , τ
  append-both : {Γ : Ctx (k + ℓ)}
              → k by Γ ⊂' Γ'
              → suc k by Γ , τ ⊂' Γ' , R.act-τ (ext-k' k suc) τ

ext-k'-suc-commute : (k : ℕ)
                   → (τ : SType (k + ℓ))
                   → R.act-τ (R.ext (ext-k' k suc)) (R.act-τ suc τ) ≡ R.act-τ suc (R.act-τ (ext-k' k suc) τ)
ext-k'-suc-commute k τ
  rewrite R.act-τ-distr suc (R.ext (ext-k' k suc)) τ
        | R.act-τ-distr (ext-k' k suc) suc τ
        = refl

∈-thinning : {Γ : Ctx (k + ℓ)}
           → k by Γ ⊂' Γ'
           → τ ∈ Γ at ι
           → R.act-τ (ext-k' k suc) τ ∈ Γ' at ext-k' k suc ι
∈-thinning ignore-head ∈ = ∈-suc refl ∈
∈-thinning (append-both {k = k} {τ = τ} Γ⊂Γ') (∈-zero refl) = ∈-zero (ext-k'-suc-commute k τ)
∈-thinning (append-both {k = k} Γ⊂Γ') (∈-suc {τ = τ} refl ∈) = ∈-suc (ext-k'-suc-commute k τ) (∈-thinning Γ⊂Γ' ∈)

mutual
  Γ⊢τ-thinning : {Γ : Ctx (k + ℓ)}
               → (Γ⊂Γ' : k by Γ ⊂' Γ')
               → Γ' ok
               → Γ ⊢ τ
               → Γ' ⊢ R.act-τ (ext-k' k suc) τ
  Γ⊢τ-thinning Γ⊂Γ' Γ'ok (TWF-TrueRef _) = TWF-TrueRef Γ'ok
  Γ⊢τ-thinning Γ⊂Γ' Γ'ok (TWF-Base ε₁δ ε₂δ) =
    TWF-Base
      (Γ⊢ε⦂τ-thinning (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₁δ)
      (Γ⊢ε⦂τ-thinning (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₂δ)
  Γ⊢τ-thinning Γ⊂Γ' Γ'ok (TWF-Conj δ₁ δ₂) = TWF-Conj (Γ⊢τ-thinning Γ⊂Γ' Γ'ok δ₁) (Γ⊢τ-thinning Γ⊂Γ' Γ'ok δ₂)
  Γ⊢τ-thinning Γ⊂Γ' Γ'ok (TWF-Arr δ₁ δ₂) =
    TWF-Arr
      (Γ⊢τ-thinning Γ⊂Γ' Γ'ok δ₁)
      (Γ⊢τ-thinning (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (Γ⊢τ-thinning Γ⊂Γ' Γ'ok δ₁)) δ₂)
  Γ⊢τ-thinning {k = k} Γ⊂Γ' Γ'ok (TWF-ADT consδs) = TWF-ADT (thin-cons Γ⊂Γ' Γ'ok consδs)
    where
    thin-cons : (k by Γ ⊂' Γ')
              → Γ' ok
              → {cons : ADTCons nₐ (k + ℓ)}
              → All (Γ ⊢_) cons
              → All (Γ' ⊢_) (R.act-cons (ext-k' k suc) cons)
    thin-cons Γ⊂Γ' Γ'ok [] = []
    thin-cons Γ⊂Γ' Γ'ok (δ ∷ consδs) = Γ⊢τ-thinning Γ⊂Γ' Γ'ok δ ∷ thin-cons Γ⊂Γ' Γ'ok consδs

  Γ⊢ε⦂τ-thinning : {Γ : Ctx (k + ℓ)}
                 → (Γ⊂Γ' : k by Γ ⊂' Γ')
                 → Γ' ok
                 → Γ ⊢ ε ⦂ τ
                 → Γ' ⊢ R.act-ε (ext-k' k suc) ε ⦂ R.act-τ (ext-k' k suc) τ
  Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok (T-Unit _) = T-Unit Γ'ok
  Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok (T-Var Γok ∈) = T-Var Γ'ok (∈-thinning Γ⊂Γ' ∈)
  Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok (T-Abs arrδ@(TWF-Arr domδ codδ) δ) =
    T-Abs
      (Γ⊢τ-thinning Γ⊂Γ' Γ'ok arrδ)
      (Γ⊢ε⦂τ-thinning (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (Γ⊢τ-thinning Γ⊂Γ' Γ'ok domδ)) δ)
  Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok (T-App δ₁ δ₂) = {! T-App !}
  Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok (T-Case resδ δ₁ branches-well-typed) = {! !}
  Γ⊢ε⦂τ-thinning {k = k} Γ⊂Γ' Γ'ok (T-Con {ε = ε} {ι = ι} {cons = cons} refl δ adtτ) =
    let δ' = Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok δ
        δ-substed = subst (λ τ → _ ⊢ R.act-ε (ext-k' k suc) ε ⦂ τ) (R.cons-lookup-comm (ext-k' k suc) ι cons) δ'
     in T-Con
          refl
          δ-substed
          (Γ⊢τ-thinning Γ⊂Γ' Γ'ok adtτ)
  Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok (T-Sub δ₁ τ'δ <:) = {! !}
  Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok (T-RConv δ₁ τ'δ τ~τ') = {! !}

Γ⊢ε⦂τ-weakening : Γ ok
                → Γ ⊢ τ'
                → Γ ⊢ ε ⦂ τ
                → (Γ , τ') ⊢ R.weaken-ε ε ⦂ R.weaken-τ τ
Γ⊢ε⦂τ-weakening Γok Γ⊢τ' Γ⊢ε⦂τ = Γ⊢ε⦂τ-thinning ignore-head (TCTX-Bind Γok Γ⊢τ') Γ⊢ε⦂τ
