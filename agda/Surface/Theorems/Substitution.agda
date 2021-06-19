{-# OPTIONS --safe #-}

module Surface.Theorems.Substitution where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (suc; zero; fromℕ<; raise)
open import Data.Nat.Base using (suc; zero; _+_)
open import Data.Nat.Properties using (≤-stepsʳ; ≤-refl; m≢1+n+m; suc-injective)
open import Data.Product renaming (_,_ to _,'_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

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
open import Surface.Operational.BetaEquivalence
open import Surface.Derivations
open import Surface.Theorems.Thinning

-- Substitution lemmas

-- Some local helpers

[_↦τ<_]_ : ∀ ℓ
         → (ε : STerm ℓ) → SType (suc k + ℓ) → SType (k + ℓ)
[_↦τ<_]_ {k = k} _ ε τ = [ ctx-idx k ↦τ R.weaken-ε-k _ ε ] τ

[_↦ε<_]_ : ∀ ℓ
         → (ε : STerm ℓ) → STerm (suc k + ℓ) → STerm (k + ℓ)
[_↦ε<_]_ {k = k} _ ε ε' = [ ctx-idx k ↦ε R.weaken-ε-k _ ε ] ε'

[_↦c<_]_ : ∀ ℓ
         → (ε : STerm ℓ) → ADTCons nₐ (suc k + ℓ) → ADTCons nₐ (k + ℓ)
[_↦c<_]_ {k = k} _ ε cons = [ ctx-idx k ↦c R.weaken-ε-k _ ε ] cons

[_↦bs<_]_ : ∀ ℓ
         → (ε : STerm ℓ) → CaseBranches nₐ (suc k + ℓ) → CaseBranches nₐ (k + ℓ)
[_↦bs<_]_ {k = k} _ ε bs = [ ctx-idx k ↦bs R.weaken-ε-k _ ε ] bs

weaken-↦<-suc-comm-τ : ∀ {k ℓ} {τ : SType (suc k + ℓ)} (ε : STerm ℓ)
                     → [ ℓ ↦τ< ε ] weaken-τ τ ≡ weaken-τ ([ ℓ ↦τ< ε ] τ)
weaken-↦<-suc-comm-τ {k} {ℓ} {τ} ε
  rewrite ρ-σ-distr-τ suc (replace-at (ctx-idx k) (weaken-ε-k k ε)) τ
        | σ-ρ-distr-τ (replace-at (suc (ctx-idx k)) (weaken-ε-k (suc k) ε)) suc τ
        | S.act-τ-extensionality (weaken-replace-comm (weaken-ε-k k ε) (ctx-idx k)) τ
        | weaken-ε-suc-k k ε
        = refl

var-earlier-in-Γ-remains : (Δ : ,-CtxSuffix ℓ σ k)
                         → τ ∈ Γ ,σ, Δ at ι
                         → (k<ι : ctx-idx k < ι)
                         → [ ℓ ↦τ< ε ] τ ∈ Γ ++ [↦Δ ε ] Δ at m<n-n-pred k<ι
var-earlier-in-Γ-remains {ε = ε}
                         [ _ ]   (∈-suc {τ = τ} refl ∈) (<-zero _) rewrite replace-weakened-τ-zero (R.weaken-ε-k zero ε) τ = ∈
var-earlier-in-Γ-remains {ι = (suc (suc _))} {ε = ε}
                         (Δ , _) (∈-suc {τ = τ} refl ∈) (<-suc k<ι) = ∈-suc (weaken-↦<-suc-comm-τ ε) (var-earlier-in-Γ-remains Δ ∈ k<ι)

var-later-in-Γ-remains : (Δ : ,-CtxSuffix ℓ σ k)
                       → τ ∈ Γ ,σ, Δ at ι
                       → (k>ι : ctx-idx k > ι)
                       → [ ctx-idx k ↦τ R.weaken-ε-k k ε ] τ ∈ Γ ++ [↦Δ ε ] Δ at tighten k>ι
var-later-in-Γ-remains {ε = ε} (Δ , τ) (∈-zero refl) (<-zero _) = ∈-zero (weaken-↦<-suc-comm-τ ε)
var-later-in-Γ-remains {ε = ε} (Δ , _) (∈-suc {τ = τ} refl ∈) (<-suc k>ι) = ∈-suc (weaken-↦<-suc-comm-τ ε) (var-later-in-Γ-remains Δ ∈ k>ι)

-- Referred to as typing-substitution in the paper
mutual
  sub-Γok : (Δ : ,-CtxSuffix ℓ σ k)
          → Γ ⊢ ε ⦂ σ
          → (Γ ,σ, Δ) ok
          → (Γ ++ [↦Δ ε ] Δ) ok
  sub-Γok [ _ ] εδ (TCTX-Bind Γ-ok _) = Γ-ok
  sub-Γok (Δ , τ) εδ (TCTX-Bind Γ,σ,Δ-ok τδ) = TCTX-Bind (sub-Γok Δ εδ Γ,σ,Δ-ok) (sub-Γ⊢τ Δ εδ τδ)

  sub-Γ⊢τ : (Δ : ,-CtxSuffix ℓ σ k)
          → Γ ⊢ ε ⦂ σ
          → Γ ,σ, Δ ⊢ τ
          → Γ ++ [↦Δ ε ] Δ ⊢ [ ℓ ↦τ< ε ] τ
  sub-Γ⊢τ Δ εδ (TWF-TrueRef Γok) = TWF-TrueRef (sub-Γok Δ εδ Γok)
  sub-Γ⊢τ {k = k} {ε = ε}
          Δ εδ (TWF-Base {ε₁ = ε₁} {ε₂ = ε₂} ε₁δ ε₂δ)
    rewrite S.act-ε-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) ε₁
          | S.act-ε-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) ε₂
          | R.act-ε-distr (raise k) suc ε
          = let ε₁δ' = sub-Γ⊢ε⦂τ (Δ , _) εδ ε₁δ
                ε₂δ' = sub-Γ⊢ε⦂τ (Δ , _) εδ ε₂δ
             in TWF-Base ε₁δ' ε₂δ'
  sub-Γ⊢τ Δ εδ (TWF-Conj ρ₁δ ρ₂δ) = TWF-Conj (sub-Γ⊢τ Δ εδ ρ₁δ) (sub-Γ⊢τ Δ εδ ρ₂δ)
  sub-Γ⊢τ {k = k} {ε = ε}
          Δ εδ (TWF-Arr {τ₂ = τ₂} arrδ resδ)
    rewrite S.act-τ-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) τ₂
          | R.act-ε-distr (raise k) suc ε
          = TWF-Arr (sub-Γ⊢τ Δ εδ arrδ) (sub-Γ⊢τ (Δ , _) εδ resδ)
  sub-Γ⊢τ Δ εδ (TWF-ADT consδs) = TWF-ADT (sub-cons Δ εδ consδs)
    where
      sub-cons : {cons : ADTCons nₐ _}
               → (Δ : ,-CtxSuffix ℓ σ k)
               → Γ ⊢ ε ⦂ σ
               → All (λ conτ → Γ ,σ, Δ ⊢ conτ) cons
               → All (λ conτ → Γ ++ [↦Δ ε ] Δ ⊢ conτ) ([ ctx-idx k ↦c R.weaken-ε-k k ε ] cons)
      sub-cons _ _ [] = []
      sub-cons Δ εδ (px ∷ pxs) = sub-Γ⊢τ Δ εδ px ∷ sub-cons Δ εδ pxs

  sub-Γ⊢ε⦂τ : (Δ : ,-CtxSuffix ℓ σ k)
            → Γ ⊢ ε ⦂ σ
            → Γ ,σ, Δ ⊢ ε₀ ⦂ τ
            → Γ ++ [↦Δ ε ] Δ ⊢ [ ℓ ↦ε< ε ] ε₀ ⦂ [ ℓ ↦τ< ε ] τ
  sub-Γ⊢ε⦂τ Δ εδ (T-Unit Γok) = T-Unit (sub-Γok Δ εδ Γok)
  sub-Γ⊢ε⦂τ {σ = σ} {k = k} {ε = ε}
            Δ εδ (T-Var {ι = ι} Γok τ-∈) with ctx-idx k <>? ι
  ... | less rep<var = T-Var (sub-Γok Δ εδ Γok) (var-earlier-in-Γ-remains Δ τ-∈ rep<var)
  ... | equal refl rewrite ∈-at-concat-point Δ τ-∈
                         | replace-weakened-τ k (weaken-ε-k k ε) σ
                         = t-weakening-suffix (sub-Γok Δ εδ Γok) εδ
  ... | greater rep>var = T-Var (sub-Γok Δ εδ Γok) (var-later-in-Γ-remains Δ τ-∈ rep>var)
  sub-Γ⊢ε⦂τ {k = k} {Γ = Γ} {ε = ε}
            Δ εδ (T-Abs {τ₁ = τ₁} {τ₂ = τ₂} {ε = ε'} arrδ bodyδ) = T-Abs (sub-Γ⊢τ Δ εδ arrδ) bodyδ'
    where
      bodyδ' : Γ ++ [↦Δ ε ] (Δ , τ₁) ⊢
               S.act-ε (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) ε' ⦂
               S.act-τ (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) τ₂
      bodyδ' rewrite S.act-τ-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) τ₂
                   | S.act-ε-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) ε'
                   | R.act-ε-distr (raise k) suc ε
                   = sub-Γ⊢ε⦂τ ( Δ , _ ) εδ bodyδ
  sub-Γ⊢ε⦂τ {ℓ = ℓ} {k = k} {Γ = Γ} {ε = ε}
            Δ εδ (T-App {ε₁ = ε₁} {τ₁} {τ₂} {ε₂} ε₁δ ε₂δ)
    rewrite subst-commutes-τ-zero (ctx-idx k) (R.weaken-ε-k _ ε) ε₂ τ₂
          = T-App ε₁δ' (sub-Γ⊢ε⦂τ Δ εδ ε₂δ)
    where
      ε₁δ' : Γ ++ [↦Δ ε ] Δ ⊢
             [ ℓ ↦ε< ε ] ε₁ ⦂
             ([ ℓ ↦τ< ε ] τ₁) ⇒ ([ suc (ctx-idx k) ↦τ R.weaken-ε (R.weaken-ε-k k ε) ] τ₂)
      ε₁δ' rewrite sym (S.act-τ-extensionality (ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) τ₂) = sub-Γ⊢ε⦂τ Δ εδ ε₁δ
  sub-Γ⊢ε⦂τ {ℓ = ℓ} {k = k} {Γ = Γ} {ε = ε} Δ εδ (T-Case resδ ε₀δ branches)
    = T-Case (sub-Γ⊢τ Δ εδ resδ) (sub-Γ⊢ε⦂τ Δ εδ ε₀δ) (sub-branches branches)
    where
      sub-branches : ∀ {bs : CaseBranches nₐ (suc k + ℓ)} {cons : ADTCons nₐ (suc k + ℓ)}
                   → BranchesHaveType (Γ ,σ, Δ) cons bs τ
                   → BranchesHaveType (Γ ++ [↦Δ ε ] Δ) ([ ℓ ↦c< ε ] cons) ([ ℓ ↦bs< ε ] bs) ([ ℓ ↦τ< ε ] τ)
      sub-branches NoBranches = NoBranches
      sub-branches {τ = τ} (OneMoreBranch {ε' = ε'} {conτ = conτ} branch-εδ bs) = OneMoreBranch branch-εδ' (sub-branches bs)
        where
          branch-εδ' : Γ ++ [↦Δ ε ] (Δ , conτ) ⊢
                       S.act-ε (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) ε' ⦂
                       weaken-τ ([ ℓ ↦τ< ε ] τ)
          branch-εδ' rewrite sym (weaken-↦<-suc-comm-τ {τ = τ} ε)
                           | S.act-ε-extensionality (ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) ε'
                           | R.act-ε-distr (raise k) suc ε
                           = sub-Γ⊢ε⦂τ (Δ , conτ) εδ branch-εδ
  sub-Γ⊢ε⦂τ Δ εδ (T-Con {cons = cons} ≡-prf conδ adtτ)
    = T-Con (S.act-cons-member _ cons ≡-prf) (sub-Γ⊢ε⦂τ Δ εδ conδ) (sub-Γ⊢τ Δ εδ adtτ)
  sub-Γ⊢ε⦂τ Δ εδ (T-Sub εδ' τ'δ <:) = T-Sub (sub-Γ⊢ε⦂τ Δ εδ εδ') (sub-Γ⊢τ Δ εδ τ'δ) (sub-Γ⊢τ<:τ' Δ εδ <:)
  sub-Γ⊢ε⦂τ {k = k} {ε = ε} Δ εδ (T-RConv εδ' τ'δ τ~τ')
    = let sub-τ~τ' = ↦τ-preserves-↭βτ (ctx-idx k) (R.act-ε (raise k) ε) τ~τ'
       in T-RConv (sub-Γ⊢ε⦂τ Δ εδ εδ') (sub-Γ⊢τ Δ εδ τ'δ) sub-τ~τ'

  sub-Γ⊢τ<:τ' : (Δ : ,-CtxSuffix ℓ σ k)
              → Γ ⊢ ε ⦂ σ
              → Γ ,σ, Δ ⊢ τ <: τ'
              → Γ ++ [↦Δ ε ] Δ ⊢ [ ℓ ↦τ< ε ] τ <: [ ℓ ↦τ< ε ] τ'
  sub-Γ⊢τ<:τ' Δ εδ (ST-Base oracle x) = ST-Base oracle (Oracle.subst oracle x)
  sub-Γ⊢τ<:τ' {k = k} {Γ = Γ} {ε = ε} Δ εδ (ST-Arr {τ₂ = τ₂} {τ₂' = τ₂'} <:₁ <:₂ δτ₁⇒τ₂ δτ₁')
    = ST-Arr (sub-Γ⊢τ<:τ' Δ εδ <:₁) <:₂' (sub-Γ⊢τ Δ εδ δτ₁⇒τ₂) (sub-Γ⊢τ Δ εδ δτ₁')
    where
      <:₂' : (Γ ++ ([↦Δ ε ] (Δ , _))) ⊢
             S.act-τ (S.ext (replace-at (ctx-idx k) (weaken-ε-k k ε))) τ₂ <:
             S.act-τ (S.ext (replace-at (ctx-idx k) (weaken-ε-k k ε))) τ₂'
      <:₂' rewrite S.act-τ-extensionality (ext-replace-comm (weaken-ε-k k ε) (ctx-idx k)) τ₂
                 | S.act-τ-extensionality (ext-replace-comm (weaken-ε-k k ε) (ctx-idx k)) τ₂'
                 | R.act-ε-distr (raise k) suc ε
                 = sub-Γ⊢τ<:τ' (Δ , _) εδ <:₂

sub-Γ⊢ε⦂τ-front : {Γ : Ctx ℓ}
                → Γ ⊢ ϖ ⦂ σ
                → Γ , σ ⊢ ε ⦂ τ
                → Γ ⊢ [ zero ↦ε ϖ ] ε ⦂ [ zero ↦τ ϖ ] τ
sub-Γ⊢ε⦂τ-front {ϖ = ϖ} ϖδ εδ with sub-Γ⊢ε⦂τ [ _ ] ϖδ εδ
... | full rewrite R.act-ε-id (λ _ → refl) ϖ = full

sub-Γ⊢τ-front : {Γ : Ctx ℓ}
              → Γ ⊢ ε ⦂ σ
              → Γ , σ ⊢ τ
              → Γ ⊢ [ zero ↦τ ε ] τ
sub-Γ⊢τ-front {ε = ε} εδ τδ with sub-Γ⊢τ [ _ ] εδ τδ
... | full rewrite R.act-ε-id (λ _ → refl) ε = full
