{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Substitution where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (suc; zero; fromℕ<; raise)
open import Data.Nat.Base using (suc; zero; _+_)
open import Data.Nat.Properties using (≤-stepsʳ; ≤-refl; m≢1+n+m; suc-injective)
open import Data.Vec.Base using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Common.Helpers
open import Data.Fin.Extra

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Membership
open import Surface.Syntax.Renaming as R
open import Surface.Syntax.Substitution as S
open import Surface.Syntax.Substitution using ([_↦τ_]_; [_↦ε_]_; [_↦c_]_)
open import Surface.Syntax.Substitution.Stable
open import Surface.Syntax.Substitution.Distributivity as S
open import Surface.Syntax.Substitution.Commutativity
open import Surface.Derivations.Common.Theorems.Substitution.Helpers
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Agreement.Lemmas
open import Surface.Derivations.Algorithmic.Theorems.Thinning
open import Surface.Derivations.Algorithmic.Theorems.Subtyping

module _ {σε : STerm ℓ} (σεδ : Γ ⊢[ θ , M of t-sub ] σε ⦂ σ) where mutual
  sub-Γok : (Δ : ,-CtxSuffix ℓ σ k)
          → (Γ ,σ, Δ) ok[ θ , M ]
          → (Γ ++ [↦Δ σε ] Δ) ok[ θ , M ]
  sub-Γok [ _ ] (TCTX-Bind Γ-ok _) = Γ-ok
  sub-Γok (Δ , τ) (TCTX-Bind Γ,σ,Δ-ok τδ) = TCTX-Bind (sub-Γok Δ Γ,σ,Δ-ok) (sub-Γ⊢τ Δ τδ)

  sub-Γ⊢τ : (Δ : ,-CtxSuffix ℓ σ k)
          → Γ ,σ, Δ ⊢[ θ , M ] τ
          → Γ ++ [↦Δ σε ] Δ ⊢[ θ , M ] [ ℓ ↦τ< σε ] τ
  sub-Γ⊢τ Δ (TWF-TrueRef Γok) = TWF-TrueRef (sub-Γok Δ Γok)
  sub-Γ⊢τ {k = k} Δ (TWF-Base {ε₁ = ε₁} {ε₂ = ε₂} ε₁δ ε₂δ)
    rewrite S.act-ε-extensionality (S.ext-replace-comm (R.weaken-ε-k k σε) (ctx-idx k)) ε₁
          | S.act-ε-extensionality (S.ext-replace-comm (R.weaken-ε-k k σε) (ctx-idx k)) ε₂
          | R.act-ε-distr (raise k) suc σε
          = TWF-Base (sub-Γ⊢ε⦂τ (Δ , _) ε₁δ) (sub-Γ⊢ε⦂τ (Δ , _) ε₂δ)
  sub-Γ⊢τ Δ (TWF-Conj τ₁δ τ₂δ) = TWF-Conj (sub-Γ⊢τ Δ τ₁δ) (sub-Γ⊢τ Δ τ₂δ)
  sub-Γ⊢τ {k = k} Δ (TWF-Arr {τ₂ = τ₂} τ₁δ τ₂δ)
    rewrite S.act-τ-extensionality (S.ext-replace-comm (R.weaken-ε-k k σε) (ctx-idx k)) τ₂
          | R.act-ε-distr (raise k) suc σε
          = TWF-Arr (sub-Γ⊢τ Δ τ₁δ) (sub-Γ⊢τ (Δ , _) τ₂δ)
  sub-Γ⊢τ Δ (TWF-ADT consδs) = TWF-ADT (sub-cons Δ consδs)

  sub-cons : {cons : ADTCons nₐ _}
           → (Δ : ,-CtxSuffix ℓ σ k)
           → All (λ conτ → Γ ,σ, Δ ⊢[ θ , M ] conτ) cons
           → All (λ conτ → Γ ++ [↦Δ σε ] Δ ⊢[ θ , M ] conτ) ([ ctx-idx k ↦c R.weaken-ε-k k σε ] cons)
  sub-cons Δ [] = []
  sub-cons Δ (τδ ∷ τδs) = sub-Γ⊢τ Δ τδ ∷ sub-cons Δ τδs

  sub-branches : {cons : ADTCons nₐ _}
               → {bs : CaseBranches nₐ _}
               → (Δ : ,-CtxSuffix ℓ σ k)
               → BranchesHaveType θ M (Γ ,σ, Δ) cons bs τ
               → BranchesHaveType θ M (Γ ++ [↦Δ σε ] Δ) ([ ℓ ↦c< σε ] cons) ([ ℓ ↦bs< σε ] bs) ([ ℓ ↦τ< σε ] τ)
  sub-branches Δ NoBranches = NoBranches
  sub-branches {k = k} Δ (OneMoreBranch {ε = ε} {τ = τ} εδ bsδ)
    with εδ' ← sub-Γ⊢ε⦂τ (Δ , _) εδ
    rewrite S.act-ε-extensionality (S.ext-replace-comm (R.weaken-ε-k k σε) (ctx-idx k)) ε
          | R.act-ε-distr (raise k) suc σε
          = let εδ' = subst (_ ⊢[ _ , _ of _ ] _ ⦂_) (weaken-↦<-suc-comm-τ τ σε) εδ'
             in OneMoreBranch εδ' (sub-branches Δ bsδ)

  sub-Γ⊢ε⦂τ : (Δ : ,-CtxSuffix ℓ σ k)
            → Γ ,σ, Δ ⊢[ θ , M of κ ] ε₀ ⦂ τ
            → Γ ++ [↦Δ σε ] Δ ⊢[ θ , M of t-sub ] [ ℓ ↦ε< σε ] ε₀ ⦂ [ ℓ ↦τ< σε ] τ
  sub-Γ⊢ε⦂τ Δ (T-Unit Γok) = as-sub (T-Unit (sub-Γok Δ Γok))
  sub-Γ⊢ε⦂τ {k = k} Δ (T-Var {ι = ι} Γok ∈)
    with ctx-idx k <>? ι
  ... | less k<ι = as-sub (T-Var (sub-Γok Δ Γok) (var-earlier-in-Γ-remains Δ ∈ k<ι))
  ... | equal refl rewrite ∈-at-concat-point Δ ∈
                         | replace-weakened-τ k (weaken-ε-k k σε) σ
                         = Γ⊢ε⦂τ-weakening-suffix (sub-Γok Δ Γok) σεδ
  ... | greater k>ι = as-sub (T-Var (sub-Γok Δ Γok) (var-later-in-Γ-remains Δ ∈ k>ι))
  sub-Γ⊢ε⦂τ {k = k} Δ (T-Abs {τ₁ = τ₁} {ε = ε'} {τ₂ = τ₂} bodyδ)
    rewrite S.act-τ-extensionality (S.ext-replace-comm (R.weaken-ε-k k σε) (ctx-idx k)) τ₂
          | S.act-ε-extensionality (S.ext-replace-comm (R.weaken-ε-k k σε) (ctx-idx k)) ε'
          | R.act-ε-distr (raise k) suc σε
    with T-Sub bodyδ' <:δ ← sub-Γ⊢ε⦂τ (Δ , _) bodyδ
       = T-Sub
          (T-Abs bodyδ')
          (Γ⊢τ'<:τ-⇒-Γ⊢τ₀⇒τ'<:τ₀⇒τ <:δ)
  sub-Γ⊢ε⦂τ {k = k} Δ (T-App {ε₁ = ε₁} {τ₁} {τ₂} {ε₂} ε₁δ ε₂δ refl)
    rewrite subst-commutes-τ-zero (ctx-idx k) (R.weaken-ε-k k σε) ε₂ τ₂
    with T-Sub ε₁δ' (ST-Arr <:₁δ <:₂δ) ← sub-Γ⊢ε⦂τ Δ ε₁δ
        = let ε₂δ' = sub-Γ⊢ε⦂τ Δ ε₂δ
              <:₂δ' = sub-Γ⊢τ'<:τ-front ε₂δ' <:₂δ
              <:₂δ' = subst (λ δ → _ ⊢[ _ , _ ] _ <: [ zero ↦τ _ ] δ)
                            (S.act-τ-extensionality (ext-replace-comm (R.weaken-ε-k k σε) (ctx-idx k)) τ₂)
                            <:₂δ'
           in T-Sub
                (T-App ε₁δ' (trans-sub <:₁δ ε₂δ') refl)
                <:₂δ'
  sub-Γ⊢ε⦂τ Δ (T-Case resδ εδ bsδ) = as-sub (T-Case (sub-Γ⊢τ Δ resδ) (sub-Γ⊢ε⦂τ Δ εδ) (sub-branches Δ bsδ))
  sub-Γ⊢ε⦂τ {k = k} Δ (T-Con {ι = ι} {cons = cons} <:-lookup-δ εδ adtτ)
    with T-Sub εδ' <:δ' ← sub-Γ⊢ε⦂τ Δ εδ
       | <:-lookup-δ' ← sub-Γ⊢τ'<:τ σεδ Δ <:-lookup-δ
    rewrite S.cons-lookup-comm (replace-at (ctx-idx k) (R.weaken-ε-k k σε)) ι cons
          = as-sub (T-Con (<:-transitive <:δ' <:-lookup-δ') εδ' (sub-Γ⊢τ Δ adtτ))
  sub-Γ⊢ε⦂τ Δ (T-Sub εδ <:δ) = trans-sub (sub-Γ⊢τ'<:τ σεδ Δ <:δ) (sub-Γ⊢ε⦂τ Δ εδ)

sub-Γ⊢τ-front : {Γ : Ctx ℓ}
              → Γ ⊢[ θ , M of t-sub ] σε ⦂ σ
              → Γ , σ ⊢[ θ , M ] τ
              → Γ ⊢[ θ , M ] [ zero ↦τ σε ] τ
sub-Γ⊢τ-front {σε = σε} σεδ τδ
  with τδ' ← sub-Γ⊢τ σεδ [ _ ] τδ
  rewrite R.act-ε-id (λ _ → refl) σε
        = τδ'

sub-Γ⊢ε⦂τ-front : {Γ : Ctx ℓ}
                → Γ ⊢[ θ , M of t-sub ] σε ⦂ σ
                → Γ , σ ⊢[ θ , M of κ ] ε ⦂ τ
                → Γ ⊢[ θ , M  of t-sub ] [ zero ↦ε σε ] ε ⦂ [ zero ↦τ σε ] τ
sub-Γ⊢ε⦂τ-front {σε = σε} σεδ εδ
  with εδ' ← sub-Γ⊢ε⦂τ σεδ [ _ ] εδ
  rewrite R.act-ε-id (λ _ → refl) σε
        = εδ'
