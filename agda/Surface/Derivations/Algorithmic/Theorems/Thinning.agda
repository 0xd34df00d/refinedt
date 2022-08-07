{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Thinning where

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
open import Surface.Derivations.Algorithmic.Theorems.Helpers
open import Surface.Derivations.Algorithmic.Theorems.Agreement.Γok
open import Surface.Derivations.Algorithmic.Theorems.Agreement.Γok.WF

∈-thinning : {Γ : Ctx (k + ℓ)}
           → k by Γ ⊂' Γ'
           → τ ∈ Γ at ι
           → R.act-τ (ext-k' k suc) τ ∈ Γ' at ext-k' k suc ι
∈-thinning ignore-head ∈ = ∈-suc refl ∈
∈-thinning (append-both {k = k} {τ = τ} Γ⊂Γ') (∈-zero refl) = ∈-zero (ext-k'-suc-commute k τ)
∈-thinning (append-both {k = k} Γ⊂Γ') (∈-suc {τ = τ} refl ∈) = ∈-suc (ext-k'-suc-commute k τ) (∈-thinning Γ⊂Γ' ∈)

<:-thinning : {Γ : Ctx (k + ℓ)}
            → (Γ⊂Γ' : k by Γ ⊂' Γ')
            → (δ : Γ ⊢[ θ , M ] τ' <: τ)
            → Γ' ⊢[ θ , M ] R.act-τ (ext-k' k suc) τ' <: R.act-τ (ext-k' k suc) τ
<:-thinning {θ = θ} Γ⊂Γ' (ST-Base is-just) = ST-Base (Oracle.thin θ Γ⊂Γ' is-just)
<:-thinning Γ⊂Γ' (ST-Arr <:₁δ <:₂δ) = ST-Arr (<:-thinning Γ⊂Γ' <:₁δ) (<:-thinning (append-both Γ⊂Γ') <:₂δ)
<:-thinning {k = k} {ℓ = ℓ} {Γ' = Γ'} {Γ = Γ} Γ⊂Γ' (ST-ADT cons-<:) = ST-ADT (go cons-<:)
  where
  go : {cons' cons : ADTCons nₐ (k + ℓ)}
     → AllSubtypes Γ  θ M cons' cons
     → AllSubtypes Γ' θ M (R.act-cons (ext-k' k suc) cons') (R.act-cons (ext-k' k suc) cons)
  go {cons' = []}    {[]}    []             = []
  go {cons' = _ ∷ _} {_ ∷ _} (τδ ∷ cons-<:) = <:-thinning Γ⊂Γ' τδ ∷ go cons-<:

mutual
  Γ⊢τ-thinning↓ : {Γ : Ctx (k + ℓ)}
                → (Γ⊂Γ' : k by Γ ⊂' Γ')
                → Γ' ok[ θ , M ]
                → (δ : Γ ⊢[ θ , M ] τ)
                → Acc _<_ (size-twf δ)
                → Γ' ⊢[ θ , M ] R.act-τ (ext-k' k suc) τ
  Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok (TWF-TrueRef _) _ = TWF-TrueRef Γ'ok
  Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok (TWF-Base ε₁δ ε₂δ) (acc rec)
    = let acc₁ = rec _ (s≤s (₁≤₂ _ _))
          acc₂ = rec _ (s≤s (₂≤₂ _ _))
       in TWF-Base
            (Γ⊢ε⦂τ-thinning↓ (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₁δ acc₁)
            (Γ⊢ε⦂τ-thinning↓ (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₂δ acc₂)
  Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok (TWF-Conj δ₁ δ₂) (acc rec)
    = let acc₁ = rec _ (s≤s (₁≤₂ _ _))
          acc₂ = rec _ (s≤s (₂≤₂ _ _))
       in TWF-Conj (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok δ₁ acc₁) (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok δ₂ acc₂)
  Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok (TWF-Arr δ₁ δ₂) (acc rec)
    = let acc₁ = rec _ (s≤s (₁≤₂ _ _))
          acc₂ = rec _ (s≤s (₂≤₂ _ _))
          δ₁' = Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok δ₁ acc₁
       in TWF-Arr
            δ₁'
            (Γ⊢τ-thinning↓ (append-both Γ⊂Γ') (TCTX-Bind Γ'ok δ₁') δ₂ acc₂)
  Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok (TWF-ADT consδs) (acc rec) = TWF-ADT (cons-thinning↓ Γ⊂Γ' Γ'ok consδs (rec _ ≤-refl))

  Γ⊢ε⦂τ-thinning↓ : {Γ : Ctx (k + ℓ)}
                  → (Γ⊂Γ' : k by Γ ⊂' Γ')
                  → Γ' ok[ θ , M ]
                  → (δ : Γ ⊢[ θ , M of κ ] ε ⦂ τ)
                  → Acc _<_ (size-t δ)
                  → Γ' ⊢[ θ , M of κ ] R.act-ε (ext-k' k suc) ε ⦂ R.act-τ (ext-k' k suc) τ
  Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok (T-Unit _) _ = T-Unit Γ'ok
  Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok (T-Var _ ∈) _ = T-Var Γ'ok (∈-thinning Γ⊂Γ' ∈)
  Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok (T-Abs εδ) (acc rec)
    with εδ-smaller ← Γ⊢ε⦂τ-⇒-Γok-smaller εδ
    with TCTX-Bind _ τ₁δ ← Γ⊢ε⦂τ-⇒-Γok εδ
       = let τ₁δ' = Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok τ₁δ (rec _ (s≤s (≤-trans (≤-stepsˡ 2 (m≤n⊔m _ _)) εδ-smaller)))
          in T-Abs (Γ⊢ε⦂τ-thinning↓ (append-both Γ⊂Γ') (TCTX-Bind Γ'ok τ₁δ') εδ (rec _ ≤-refl))
  Γ⊢ε⦂τ-thinning↓ {k = k} Γ⊂Γ' Γ'ok (T-App {τ₂ = τ₂} {ε₂ = ε₂} δ₁ δ₂ refl) (acc rec)
    rewrite ρ-subst-distr-τ-0 (ext-k' k suc) ε₂ τ₂
          = let acc₁ = rec _ (s≤s (₁≤₂ _ _))
                acc₂ = rec _ (s≤s (₂≤₂ _ _))
             in T-App
                  (Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok δ₁ acc₁)
                  (Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok δ₂ acc₂)
                  refl
  Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok (T-Case resδ δ branchesδ) (acc rec)
    = let acc₁ = rec _ (s≤s (₂≤₃ (size-t δ) _ _))
          acc₂ = rec _ (s≤s (₁≤₂ _ _))
          acc₃ = rec _ (s≤s (₃≤₃ (size-t δ) _ _))
       in T-Case
            (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok resδ acc₁)
            (Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok δ acc₂)
            (branches-thinning↓ Γ⊂Γ' Γ'ok branchesδ acc₃)
  Γ⊢ε⦂τ-thinning↓ {k = k} Γ⊂Γ' Γ'ok (T-Con {ι = ι} {cons = cons} <:δ εδ adtτ) (acc rec)
    with εδ' ← Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok εδ (rec _ (s≤s (₁≤₂ _ _)))
       | <:δ' ← <:-thinning Γ⊂Γ' <:δ
    rewrite R.cons-lookup-comm (ext-k' k suc) ι cons
          = let adtτ' = Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok adtτ (rec _ (s≤s (₂≤₂ _ _)))
             in T-Con <:δ' εδ' adtτ'
  Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok (T-Sub εδ <:δ) (acc rec)
    = T-Sub
        (Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok εδ (rec _ ≤-refl))
        (<:-thinning Γ⊂Γ' <:δ)

  cons-thinning↓ : {Γ : Ctx (k + ℓ)}
                 → {cons : ADTCons nₐ (k + ℓ)}
                 → (Γ⊂Γ' : k by Γ ⊂' Γ')
                 → Γ' ok[ θ , M ]
                 → (δs : All (Γ ⊢[ θ , M ]_) cons)
                 → Acc _<_ (size-all-cons δs)
                 → All (Γ' ⊢[ θ , M ]_) (R.act-cons (ext-k' k suc) cons)
  cons-thinning↓ Γ⊂Γ' Γ'ok [] _ = []
  cons-thinning↓ Γ⊂Γ' Γ'ok (δ ∷ consδs) (acc rec)
    = let acc₁ = rec _ (s≤s (₁≤₂ _ _))
          acc₂ = rec _ (s≤s (₂≤₂ _ _))
       in Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok δ acc₁ ∷ cons-thinning↓ Γ⊂Γ' Γ'ok consδs acc₂

  branches-thinning↓ : {Γ : Ctx (k + ℓ)}
                     → {cons : ADTCons nₐ (k + ℓ)}
                     → {bs : CaseBranches nₐ (k + ℓ)}
                     → (Γ⊂Γ' : k by Γ ⊂' Γ')
                     → Γ' ok[ θ , M ]
                     → (δs : BranchesHaveType θ M Γ cons bs τ)
                     → Acc _<_ (size-bs δs)
                     → BranchesHaveType θ M Γ' (R.act-cons (ext-k' k suc) cons) (R.act-branches (ext-k' k suc) bs) (R.act-τ (ext-k' k suc) τ)
  branches-thinning↓ Γ⊂Γ' Γ'ok NoBranches _ = NoBranches
  branches-thinning↓ {k = k} {τ = τ} Γ⊂Γ' Γ'ok (OneMoreBranch εδ branchesδ) (acc rec)
    with TCTX-Bind _ conτδ ← Γ⊢ε⦂τ-⇒-Γok εδ
    with εδ' ← (let conτ-acc = rec _ (s≤s (m≤n⇒m≤n⊔o _ (∥Γ⊢τ₁∥≤∥Γ,τ₁⊢ε⦂τ₂∥ conτδ εδ)))
                    conτδ' = Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok conτδ conτ-acc
                 in Γ⊢ε⦂τ-thinning↓ (append-both Γ⊂Γ') (TCTX-Bind Γ'ok conτδ') εδ (rec _ (s≤s (₁≤₂ _ _))))
    rewrite ext-k'-suc-commute k τ
          = OneMoreBranch
              εδ'
              (branches-thinning↓ Γ⊂Γ' Γ'ok branchesδ (rec _ (s≤s (₂≤₂ _ _))))


Γ⊢τ-thinning : {Γ : Ctx (k + ℓ)}
             → (Γ⊂Γ' : k by Γ ⊂' Γ')
             → Γ' ok[ θ , M ]
             → Γ ⊢[ θ , M ] τ
             → Γ' ⊢[ θ , M ] R.act-τ (ext-k' k suc) τ
Γ⊢τ-thinning Γ⊂Γ' [Γ'ok] δ = Γ⊢τ-thinning↓ Γ⊂Γ' [Γ'ok] δ (<-wellFounded _)

Γ⊢ε⦂τ-thinning : {Γ : Ctx (k + ℓ)}
               → (Γ⊂Γ' : k by Γ ⊂' Γ')
               → Γ' ok[ θ , M ]
               → Γ ⊢[ θ , M of κ ] ε ⦂ τ
               → Γ' ⊢[ θ , M of κ ] R.act-ε (ext-k' k suc) ε ⦂ R.act-τ (ext-k' k suc) τ
Γ⊢ε⦂τ-thinning Γ⊂Γ' [Γ'ok] δ = Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' [Γ'ok] δ (<-wellFounded _)

<:-weakening : Γ ⊢[ θ , M ] τ₁ <: τ₂
             → (Γ , τ') ⊢[ θ , M ] R.weaken-τ τ₁ <: R.weaken-τ τ₂
<:-weakening = <:-thinning ignore-head

Γ⊢τ-weakening : Γ ok[ θ , M ]
              → Γ ⊢[ θ , M ] τ'
              → Γ ⊢[ θ , M ] τ
              → (Γ , τ') ⊢[ θ , M ] R.weaken-τ τ
Γ⊢τ-weakening Γok Γ⊢τ' = Γ⊢τ-thinning ignore-head (TCTX-Bind Γok Γ⊢τ')

Γ⊢ε⦂τ-weakening : Γ ok[ θ , M ]
                → Γ ⊢[ θ , M ] τ'
                → Γ ⊢[ θ , M of κ ] ε ⦂ τ
                → (Γ , τ') ⊢[ θ , M of κ ] R.weaken-ε ε ⦂ R.weaken-τ τ
Γ⊢ε⦂τ-weakening Γok Γ⊢τ' = Γ⊢ε⦂τ-thinning ignore-head (TCTX-Bind Γok Γ⊢τ')

Γ⊢ε⦂τ-weakening-suffix : {Δ : CtxSuffix ℓ k}
                       → (Γ ++ Δ) ok[ θ , M ]
                       → Γ ⊢[ θ , M of κ ] ε ⦂ τ
                       → Γ ++ Δ ⊢[ θ , M of κ ] R.weaken-ε-k k ε ⦂ R.weaken-τ-k k τ
Γ⊢ε⦂τ-weakening-suffix {ε = ε} {τ = τ} {Δ = ⊘} Γ++Δok εδ
  rewrite R.act-ε-id (λ _ → refl) ε
        | R.act-τ-id (λ _ → refl) τ
        = εδ
Γ⊢ε⦂τ-weakening-suffix {k = suc k} {ε = ε} {τ = τ} {Δ = Δ , _} (TCTX-Bind Γ++Δok τδ) εδ
  rewrite sym (R.act-ε-distr (raise k) suc ε)
        | sym (R.act-τ-distr (raise k) suc τ)
        = Γ⊢ε⦂τ-weakening Γ++Δok τδ (Γ⊢ε⦂τ-weakening-suffix Γ++Δok εδ)
