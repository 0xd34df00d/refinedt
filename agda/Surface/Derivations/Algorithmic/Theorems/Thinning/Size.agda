{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Thinning.Size where

open import Data.Fin using (zero; suc; raise; #_)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Data.Vec.Base using (lookup; _∷_; [])
open import Function
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; subst; sym; cong; cong₂)
open Eq.≡-Reasoning

open import Common.Helpers
open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Subcontext
open import Surface.Syntax.Membership
open import Surface.Syntax.Renaming as R
open import Surface.Syntax.Substitution as S
open import Surface.Syntax.Substitution.Distributivity
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Helpers
open import Surface.Derivations.Algorithmic.Theorems.Agreement.Γok
open import Surface.Derivations.Algorithmic.Theorems.Agreement.Γok.WF
open import Surface.Derivations.Algorithmic.Theorems.Thinning
open import Surface.Derivations.Algorithmic.Theorems.Thinning.Size.Helpers
open import Surface.Derivations.Algorithmic.Theorems.Uniqueness

mutual
  Γ⊢τ-thinning↓-size : (Γ⊂Γ' : k by Γ ⊂' Γ')
                     → (Γ'ok : Γ' ok[ θ , M ])
                     → (τδ : Γ ⊢[ θ , M ] τ)
                     → (acc : Acc _<_ (size-twf τδ))
                     → size-twf (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok τδ acc) + size-ok (Γ⊢τ-⇒-Γok τδ)
                       ≡
                       size-twf τδ + size-ok Γ'ok
  Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok (TWF-TrueRef Γok) _ = cong suc (+-comm (size-ok Γ'ok) (size-ok Γok))
  Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok (TWF-Base ε₁δ ε₂δ) (acc rec)
    with Γ,Τ-ok@(TCTX-Bind Γok (TWF-TrueRef Γok')) ← Γ⊢ε⦂τ-⇒-Γok ε₁δ
       | ε₁δ' ← Γ⊢ε⦂τ-thinning↓      (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₁δ (rec _ (s≤s (₁≤₂ _ _)))
       | ε₂δ' ← Γ⊢ε⦂τ-thinning↓      (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₂δ (rec _ (s≤s (₂≤₂ _ _)))
       | ε₁δ↓ ← Γ⊢ε⦂τ-thinning↓-size (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₁δ (rec _ (s≤s (₁≤₂ _ _)))
       | ε₂δ↓ ← Γ⊢ε⦂τ-thinning↓-size (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₂δ (rec _ (s≤s (₂≤₂ _ _)))
    rewrite unique-Γok (Γ⊢ε⦂τ-⇒-Γok ε₂δ) Γ,Τ-ok
          | unique-Γok Γok' Γok
          | m≤n⇒m⊔n≡n (n≤1+n (size-ok Γok))
          | m≤n⇒m⊔n≡n (n≤1+n (size-ok Γ'ok))
          = cong suc (⊔-+-pairwise-≡ (size-ok Γok) (size-ok Γ'ok) (un-suc (un-suc ε₁δ↓)) (un-suc (un-suc ε₂δ↓)))
  Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok (TWF-Conj τ₁δ τ₂δ) (acc rec)
    with Γok ← Γ⊢τ-⇒-Γok τ₁δ
       | τ₁δ' ← Γ⊢τ-thinning↓      Γ⊂Γ' Γ'ok τ₁δ (rec _ (s≤s (₁≤₂ _ _)))
       | τ₂δ' ← Γ⊢τ-thinning↓      Γ⊂Γ' Γ'ok τ₂δ (rec _ (s≤s (₂≤₂ _ _)))
       | τ₁δ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok τ₁δ (rec _ (s≤s (₁≤₂ _ _)))
       | τ₂δ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok τ₂δ (rec _ (s≤s (₂≤₂ _ _)))
    rewrite unique-Γok (Γ⊢τ-⇒-Γok τ₂δ) Γok
          = cong suc (⊔-+-pairwise-≡ (size-ok Γok) (size-ok Γ'ok) τ₁δ↓ τ₂δ↓)
  Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok (TWF-Arr τ₁δ τ₂δ) (acc rec)
    with Γok ← Γ⊢τ-⇒-Γok τ₁δ
       | τ₁δ' ← Γ⊢τ-thinning↓      Γ⊂Γ' Γ'ok τ₁δ (rec _ (s≤s (₁≤₂ _ _)))
       | τ₁δ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok τ₁δ (rec _ (s≤s (₁≤₂ _ _)))
    with Γ,τ₁-ok@(TCTX-Bind Γok' τ₁δ₀) ← Γ⊢τ-⇒-Γok τ₂δ
       | τ₂δ' ← Γ⊢τ-thinning↓      (append-both Γ⊂Γ') (TCTX-Bind Γ'ok τ₁δ') τ₂δ (rec _ (s≤s (₂≤₂ _ _)))
       | τ₂δ↓ ← Γ⊢τ-thinning↓-size (append-both Γ⊂Γ') (TCTX-Bind Γ'ok τ₁δ') τ₂δ (rec _ (s≤s (₂≤₂ _ _)))
    rewrite unique-Γ⊢τ τ₁δ₀ τ₁δ
          | unique-Γok Γok' Γok
          | m≤n⇒m⊔n≡n (<⇒≤ (∥Γok∥≤∥Γ⊢τ∥ Γok τ₁δ))
          | m≤n⇒m⊔n≡n (<⇒≤ (∥Γok∥≤∥Γ⊢τ∥ Γ'ok τ₁δ'))
          = let τ₂δ↓ = un-suc τ₂δ↓
             in cong suc (⊔-+-pairwise-≡ (size-ok Γok) (size-ok Γ'ok) τ₁δ↓ (lemma₁ {a' = size-twf τ₁δ'} τ₁δ↓ τ₂δ↓))
  Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok (TWF-ADT consδs@(τδ ∷ _)) (acc rec)
    with Γok ← Γ⊢τ-⇒-Γok τδ
    with consδs' ← cons-thinning↓      Γ⊂Γ'     Γ'ok consδs (rec _ ≤-refl)
       | consδs↓ ← cons-thinning↓-size Γ⊂Γ' Γok Γ'ok consδs (rec _ ≤-refl)
       = cong suc consδs↓

  cons-thinning↓-size : {cons : ADTCons (Mkℕₐ (suc n)) (k + ℓ)}
                      → (Γ⊂Γ' : k by Γ ⊂' Γ')
                      → (Γok : Γ ok[ θ , M ])
                      → (Γ'ok : Γ' ok[ θ , M ])
                      → (consδs : All (Γ ⊢[ θ , M ]_) cons)
                      → (acc : Acc _<_ (size-all-cons consδs))
                      → size-all-cons (cons-thinning↓ Γ⊂Γ' Γ'ok consδs acc) + size-ok Γok
                        ≡
                        size-all-cons consδs + size-ok Γ'ok
  cons-thinning↓-size {n = zero} Γ⊂Γ' Γok Γ'ok (τδ ∷ []) (acc rec)
    with τδ' ← Γ⊢τ-thinning↓      Γ⊂Γ' Γ'ok τδ (rec _ (s≤s (₁≤₂ _ _)))
       | τδ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok τδ (rec _ (s≤s (₁≤₂ _ _)))
    rewrite unique-Γok (Γ⊢τ-⇒-Γok τδ) Γok
          | ⊔-identityʳ (size-twf τδ')
          | ⊔-identityʳ (size-twf τδ)
          = cong suc τδ↓
  cons-thinning↓-size {n = suc _} Γ⊂Γ' Γok Γ'ok (τδ ∷ consδs) (acc rec)
    with τδ' ← Γ⊢τ-thinning↓      Γ⊂Γ' Γ'ok τδ (rec _ (s≤s (₁≤₂ _ _)))
       | τδ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok τδ (rec _ (s≤s (₁≤₂ _ _)))
       | consδs' ← cons-thinning↓      Γ⊂Γ'     Γ'ok consδs (rec _ (s≤s (₂≤₂ _ _)))
       | consδs↓ ← cons-thinning↓-size Γ⊂Γ' Γok Γ'ok consδs (rec _ (s≤s (₂≤₂ _ _)))
    rewrite unique-Γok (Γ⊢τ-⇒-Γok τδ) Γok
          = cong suc (⊔-+-pairwise-≡ (size-ok Γok) (size-ok Γ'ok) τδ↓ consδs↓)

  branches-thinning↓-size : {cons : ADTCons (Mkℕₐ (suc n)) (k + ℓ)}
                          → {bs : CaseBranches (Mkℕₐ (suc n)) (k + ℓ)}
                          → (Γ⊂Γ' : k by Γ ⊂' Γ')
                          → (Γok : Γ ok[ θ , M ])
                          → (Γ'ok : Γ' ok[ θ , M ])
                          → (δs : BranchesHaveType θ M Γ cons bs τ)
                          → (acc : Acc _<_ (size-bs δs))
                          → size-bs (branches-thinning↓ Γ⊂Γ' Γ'ok δs acc) + size-ok Γok
                            ≡
                            size-bs δs + size-ok Γ'ok
  branches-thinning↓-size {n = n} {k = k} {τ = τ} Γ⊂Γ' Γok Γ'ok (OneMoreBranch εδ δs) (acc rec)
    with TCTX-Bind _ conτδ ← Γ⊢ε⦂τ-⇒-Γok εδ
    with conτ-acc ← rec _ (s≤s (m≤n⇒m≤n⊔o _ (∥Γ⊢τ₁∥≤∥Γ,τ₁⊢ε⦂τ₂∥ conτδ εδ)))
    with conτδ' ← Γ⊢τ-thinning↓      Γ⊂Γ' Γ'ok conτδ conτ-acc
       | conτδ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok conτδ conτ-acc
    with εδ' ← Γ⊢ε⦂τ-thinning↓      (append-both Γ⊂Γ') (TCTX-Bind Γ'ok conτδ') εδ (rec _ (s≤s (₁≤₂ _ _)))
       | εδ↓ ← Γ⊢ε⦂τ-thinning↓-size (append-both Γ⊂Γ') (TCTX-Bind Γ'ok conτδ') εδ (rec _ (s≤s (₁≤₂ _ _)))
    rewrite ext-k'-suc-commute k τ
          | unique-Γok (Γ⊢τ-⇒-Γok conτδ) Γok
          | unique-Γok (Γ⊢ε⦂τ-⇒-Γok εδ) (TCTX-Bind Γok conτδ)
          | ∥Γ,τ-ok∥≡∥τδ∥ (TCTX-Bind Γok conτδ) conτδ
          | ∥Γ,τ-ok∥≡∥τδ∥ (TCTX-Bind Γ'ok conτδ') conτδ'
    with δs
  ... | NoBranches
        rewrite ⊔-identityʳ (size-t εδ')
              | ⊔-identityʳ (size-t εδ)
              = cong suc (lemma₂ conτδ↓ εδ↓)
  ... | δs@(OneMoreBranch εδ₁ δs₁)
        with δs'@(OneMoreBranch εδ₁' δs₁') ← branches-thinning↓      Γ⊂Γ'     Γ'ok δs (rec _ (s≤s (₂≤₂ _ _)))
           | δs↓                           ← branches-thinning↓-size Γ⊂Γ' Γok Γ'ok δs (rec _ (s≤s (₂≤₂ _ _)))
           = cong suc (⊔-+-pairwise-≡ (size-ok Γok) (size-ok Γ'ok) (lemma₂ conτδ↓ εδ↓) δs↓)

  Γ⊢ε⦂τ-thinning↓-size : (Γ⊂Γ' : k by Γ ⊂' Γ')
                       → (Γ'ok : Γ' ok[ θ , M ])
                       → (εδ : Γ ⊢[ θ , M of κ ] ε ⦂ τ)
                       → (acc : Acc _<_ (size-t εδ))
                       → size-t (Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok εδ acc) + size-ok (Γ⊢ε⦂τ-⇒-Γok εδ)
                         ≡
                         size-t εδ + size-ok Γ'ok
  Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok (T-Unit Γok) _ = cong (2 +_) (+-comm (size-ok Γ'ok) (size-ok Γok))
  Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok (T-Var Γok _) _ = cong suc (+-comm (size-ok Γ'ok) (size-ok Γok))
  Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok (T-Abs εδ) (acc rec)
    with εδ-smaller ← Γ⊢ε⦂τ-⇒-Γok-smaller εδ
    with TCTX-Bind Γok τ₁δ ← Γ⊢ε⦂τ-⇒-Γok εδ
    with τ₁δ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok τ₁δ (rec _ (s≤s (≤-trans (≤-stepsˡ 2 (m≤n⊔m _ _)) εδ-smaller)))
    with τ₁δ' ← Γ⊢τ-thinning↓      Γ⊂Γ' Γ'ok τ₁δ (rec _ (s≤s (≤-trans (≤-stepsˡ 2 (m≤n⊔m _ _)) εδ-smaller)))
    with εδ↓ ← Γ⊢ε⦂τ-thinning↓-size (append-both Γ⊂Γ') (TCTX-Bind Γ'ok τ₁δ') εδ (rec _ ≤-refl)
    with εδ' ← Γ⊢ε⦂τ-thinning↓      (append-both Γ⊂Γ') (TCTX-Bind Γ'ok τ₁δ') εδ (rec _ ≤-refl)
    rewrite unique-Γok (Γ⊢τ-⇒-Γok τ₁δ) Γok
    with TCTX-Bind Γok₁ τ₁δ₁ ← Γ⊢ε⦂τ-⇒-Γok εδ
    rewrite ∥Γ,τ-ok∥≡∥τδ∥ (TCTX-Bind Γok₁ τ₁δ₁) τ₁δ
          | ∥Γ,τ-ok∥≡∥τδ∥ (TCTX-Bind Γ'ok τ₁δ') τ₁δ'
    rewrite unique-Γok Γok₁ Γok
          | unique-Γ⊢τ τ₁δ₁ τ₁δ
          = cong suc (lemma₂ τ₁δ↓ εδ↓)
  Γ⊢ε⦂τ-thinning↓-size {k = k} Γ⊂Γ' Γ'ok (T-App {τ₂ = τ₂} {ε₂ = ε₂} ε₁δ ε₂δ refl) (acc rec)
    rewrite ρ-subst-distr-τ-0 (ext-k' k suc) ε₂ τ₂
    with ε₁δ' ← Γ⊢ε⦂τ-thinning↓      Γ⊂Γ' Γ'ok ε₁δ (rec _ (s≤s (₁≤₂ _ _)))
       | ε₂δ' ← Γ⊢ε⦂τ-thinning↓      Γ⊂Γ' Γ'ok ε₂δ (rec _ (s≤s (₂≤₂ _ _)))
       | ε₁δ↓ ← Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok ε₁δ (rec _ (s≤s (₁≤₂ _ _)))
       | ε₂δ↓ ← Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok ε₂δ (rec _ (s≤s (₂≤₂ _ _)))
    with Γok ← Γ⊢ε⦂τ-⇒-Γok ε₁δ
    rewrite unique-Γok (Γ⊢ε⦂τ-⇒-Γok ε₂δ) Γok
          = cong suc (⊔-+-pairwise-≡ (size-ok Γok) (size-ok Γ'ok) ε₁δ↓ ε₂δ↓)
  Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok (T-Case resδ εδ branchesδ) (acc rec)
    with εδ' ← Γ⊢ε⦂τ-thinning↓      Γ⊂Γ' Γ'ok εδ (rec _ (s≤s (₁≤₂ _ _)))
       | εδ↓ ← Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok εδ (rec _ (s≤s (₁≤₂ _ _)))
       | resδ' ← Γ⊢τ-thinning↓      Γ⊂Γ' Γ'ok resδ (rec _ (s≤s (₂≤₃ (size-t εδ) _ _)))
       | resδ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok resδ (rec _ (s≤s (₂≤₃ (size-t εδ) _ _)))
    with Γok ← Γ⊢ε⦂τ-⇒-Γok εδ
    with branchesδ' ← branches-thinning↓      Γ⊂Γ'     Γ'ok branchesδ (rec _ (s≤s (₃≤₃ (size-t εδ) _ _)))
       | branchesδ↓ ← branches-thinning↓-size Γ⊂Γ' Γok Γ'ok branchesδ (rec _ (s≤s (₃≤₃ (size-t εδ) _ _)))
    rewrite unique-Γok (Γ⊢τ-⇒-Γok resδ) Γok
          = cong suc (⊔-+-pairwise-≡³ (size-ok Γok) (size-ok Γ'ok) εδ↓ resδ↓ branchesδ↓)
  Γ⊢ε⦂τ-thinning↓-size {k = k} Γ⊂Γ' Γ'ok (T-Con {ι = ι} {cons = cons} <:δ εδ adtτδ) (acc rec)
    with Γok ← Γ⊢ε⦂τ-⇒-Γok εδ
       | εδ' ← Γ⊢ε⦂τ-thinning↓      Γ⊂Γ' Γ'ok εδ (rec _ (s≤s (₁≤₂ _ _)))
       | εδ↓ ← Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok εδ (rec _ (s≤s (₁≤₂ _ _)))
       | <:δ' ← <:-thinning Γ⊂Γ' <:δ
    rewrite R.cons-lookup-comm (ext-k' k suc) ι cons
    with adtτδ' ← Γ⊢τ-thinning↓      Γ⊂Γ' Γ'ok adtτδ (rec _ (s≤s (₂≤₂ _ _)))
       | adtτδ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok adtτδ (rec _ (s≤s (₂≤₂ _ _)))
    rewrite unique-Γok (Γ⊢τ-⇒-Γok adtτδ) Γok
          = cong suc (⊔-+-pairwise-≡ (size-ok Γok) (size-ok Γ'ok) εδ↓ adtτδ↓)
  Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok (T-Sub εδ <:δ) (acc rec)
    = cong suc (Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok εδ (rec _ ≤-refl))

Γ⊢τ-thinning-size : (Γ⊂Γ' : k by Γ ⊂' Γ')
                  → (Γ'ok : Γ' ok[ θ , M ])
                  → (τδ : Γ ⊢[ θ , M ] τ)
                  → size-twf (Γ⊢τ-thinning Γ⊂Γ' Γ'ok τδ) + size-ok (Γ⊢τ-⇒-Γok τδ)
                    ≡
                    size-twf τδ + size-ok Γ'ok
Γ⊢τ-thinning-size Γ⊂Γ' Γ'ok τδ = Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok τδ (<-wellFounded _)

Γ⊢ε⦂τ-thinning-size : (Γ⊂Γ' : k by Γ ⊂' Γ')
                    → (Γ'ok : Γ' ok[ θ , M ])
                    → (εδ : Γ ⊢[ θ , M of κ ] ε ⦂ τ)
                    → size-t (Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok εδ) + size-ok (Γ⊢ε⦂τ-⇒-Γok εδ)
                      ≡
                      size-t εδ + size-ok Γ'ok
Γ⊢ε⦂τ-thinning-size Γ⊂Γ' Γ'ok εδ = Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok εδ (<-wellFounded _)

Γ⊢τ-weakening-size : (Γok : Γ ok[ θ , M ])
                   → (τ'δ : Γ ⊢[ θ , M ] τ')
                   → (τδ : Γ ⊢[ θ , M ] τ)
                   → size-twf (Γ⊢τ-weakening Γok τ'δ τδ) + size-ok Γok
                     ≡
                     size-twf τδ + suc (size-twf τ'δ)
Γ⊢τ-weakening-size Γok τ'δ τδ
  with size-eq ← Γ⊢τ-thinning-size ignore-head (TCTX-Bind Γok τ'δ) τδ
  rewrite ∥Γ,τ-ok∥≡∥τδ∥ (TCTX-Bind Γok τ'δ) τ'δ
        | unique-Γok (Γ⊢τ-⇒-Γok τδ) Γok
        = size-eq

Γ⊢ε⦂τ-weakening-size : (Γok : Γ ok[ θ , M ])
                   → (τ'δ : Γ ⊢[ θ , M ] τ')
                   → (εδ : Γ ⊢[ θ , M of κ ] ε ⦂ τ)
                   → size-t (Γ⊢ε⦂τ-weakening Γok τ'δ εδ) + size-ok Γok
                     ≡
                     size-t εδ + suc (size-twf τ'δ)
Γ⊢ε⦂τ-weakening-size Γok τ'δ εδ
  with size-eq ← Γ⊢ε⦂τ-thinning-size ignore-head (TCTX-Bind Γok τ'δ) εδ
  rewrite ∥Γ,τ-ok∥≡∥τδ∥ (TCTX-Bind Γok τ'δ) τ'δ
        | unique-Γok (Γ⊢ε⦂τ-⇒-Γok εδ) Γok
        = size-eq
