{-# OPTIONS --safe #-}

module Surface.Theorems.SubstTyping where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (suc; zero; fromℕ<; raise)
open import Data.Nat.Base using (suc; zero; _+_)
open import Data.Nat.Properties using (≤-stepsʳ; ≤-refl; m≢1+n+m; suc-injective)
open import Data.Product renaming (_,_ to _,'_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Data.Fin.Extra
open import Surface.WellScoped
open import Surface.WellScoped.CtxPrefix
open import Surface.WellScoped.Membership
open import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.Substitution as S
open import Surface.WellScoped.Substitution using ([_↦τ_]_; [_↦ε_]_; [_↦c_]_)
open import Surface.WellScoped.Substitution.Stable
open import Surface.WellScoped.Substitution.Distributivity as S
open import Surface.WellScoped.Substitution.Commutativity
open import Surface.Derivations
open import Surface.Theorems.Thinning

-- Substitution lemmas

-- Some local helpers

[_↦τ<_]_ : ∀ {k} ℓ
         → (ε : STerm ℓ) → SType (suc k + ℓ) → SType (k + ℓ)
[_↦τ<_]_ {k = k} _ ε τ = [ ctx-idx k ↦τ R.weaken-ε-k _ ε ] τ

[_↦ε<_]_ : ∀ {k} ℓ
         → (ε : STerm ℓ) → STerm (suc k + ℓ) → STerm (k + ℓ)
[_↦ε<_]_ {k = k} _ ε ε' = [ ctx-idx k ↦ε R.weaken-ε-k _ ε ] ε'

[_↦c<_]_ : ∀ {k} ℓ
         → (ε : STerm ℓ) → ADTCons nₐ (suc k + ℓ) → ADTCons nₐ (k + ℓ)
[_↦c<_]_ {k = k} _ ε cons = [ ctx-idx k ↦c R.weaken-ε-k _ ε ] cons

[_↦bs<_]_ : ∀ {k} ℓ
         → (ε : STerm ℓ) → CaseBranches nₐ (suc k + ℓ) → CaseBranches nₐ (k + ℓ)
[_↦bs<_]_ {k = k} _ ε bs = [ ctx-idx k ↦bs R.weaken-ε-k _ ε ] bs

weaken-↦<-τ-comm : (ι : Fin (suc ℓ))
                 → (ε : STerm ℓ)
                 → (τ : SType (suc ℓ))
                 → R.weaken-τ ([ ι ↦τ ε ] τ) ≡ [ suc ι ↦τ R.weaken-ε ε ] (R.weaken-τ τ)
weaken-↦<-τ-comm ι ε τ rewrite ρ-σ-distr-τ suc (replace-at ι ε) τ
                             | σ-ρ-distr-τ (replace-at (suc ι) (R.weaken-ε ε)) suc τ
                             | S.act-τ-extensionality (weaken-replace-comm ε ι) τ
                             = refl

∈-sucify : ∀ {k} {τ : SType ℓ} {Γ : Ctx (k + ℓ)} {τ' : SType (k + ℓ)} {ι : Fin (k + ℓ)}
         → R.weaken-τ-k (suc k) τ ∈ Γ , τ' at suc ι
         → R.weaken-τ (R.weaken-τ-k k τ) ∈ Γ , τ' at suc ι
∈-sucify {k = k} {τ = τ} {Γ = Γ} {τ' = τ'} {ι = ι} ∈ rewrite weaken-τ-suc-k k τ = ∈

var-earlier-in-Γ-remains : ∀ {k} {Γ : Ctx (suc k + ℓ)} {τ : SType (suc k + ℓ)} {ι : Fin (suc k + ℓ)} ε
                         → τ ∈ Γ at ι
                         → (k<ι : ctx-idx k < ι)
                         → [ ctx-idx k ↦τ R.weaken-ε-k k ε ] τ ∈ [ ℓ ↦Γ ε ] Γ at m<n-n-pred k<ι
var-earlier-in-Γ-remains {k = zero} ε (∈-suc {τ = τ} refl τ∈Γatι) (<-zero _) rewrite replace-weakened-τ-zero (R.weaken-ε-k zero ε) τ = τ∈Γatι
var-earlier-in-Γ-remains {k = suc k} ε (∈-suc {τ = τ} refl τ∈Γatι) (<-suc k<ι)
  rewrite sym (m<n-n-pred-cancel k<ι)
        = ∈-suc suc-≡ (var-earlier-in-Γ-remains ε τ∈Γatι (m<n⇒n<suc-pred-n k<ι))
  where
    suc-≡ : [ suc (ctx-idx k) ↦τ weaken-ε-k (suc k) ε ] weaken-τ τ ≡ weaken-τ ([ ctx-idx k ↦τ weaken-ε-k k ε ] τ)
    suc-≡ rewrite weaken-↦<-τ-comm (ctx-idx k) (weaken-ε-k k ε) τ
                | weaken-ε-suc-k k ε
                = refl

var-later-in-Γ-remains : ∀ {k} {Γ : Ctx (suc k + ℓ)} {τ : SType (suc k + ℓ)} {ι : Fin (suc k + ℓ)} ε
                       → τ ∈ Γ at ι
                       → (k>ι : ctx-idx k > ι)
                       → [ ctx-idx k ↦τ R.weaken-ε-k k ε ] τ ∈ [ ℓ ↦Γ ε ] Γ at tighten k>ι
var-later-in-Γ-remains {ℓ = ℓ} {k = suc k} {ι = zero} ε (∈-zero {τ = τ} refl) (<-zero _)
  rewrite tighten-zero (ctx-idx {ℓ} k) = ∈-zero ≡-prf
  where
    ≡-prf : [ suc (ctx-idx k) ↦τ weaken-ε-k (suc k) ε ] (weaken-τ τ) ≡ R.weaken-τ ([ ctx-idx k ↦τ weaken-ε-k k ε ] τ)
    ≡-prf rewrite weaken-↦<-τ-comm (ctx-idx k) (weaken-ε-k k ε) τ
                | weaken-ε-suc-k k ε
                = refl
var-later-in-Γ-remains {k = suc k} {ι = suc ι} ε (∈-suc {τ = τ} refl τ∈Γatι) (<-suc k>ι) = ∈-suc suc-≡ (var-later-in-Γ-remains ε τ∈Γatι k>ι)
  where
    suc-≡ : [ suc (ctx-idx k) ↦τ weaken-ε-k (suc k) ε ] weaken-τ τ ≡ weaken-τ ([ ctx-idx k ↦τ weaken-ε-k k ε ] τ)
    suc-≡ rewrite weaken-↦<-τ-comm (ctx-idx k) (weaken-ε-k k ε) τ
                | weaken-ε-suc-k k ε
                = refl

mutual
  sub-Γok : ∀ {k} {Γ : Ctx ℓ} {Γ,σ,Δ : Ctx (suc k + ℓ)}
          → Γ ⊢ ε ⦂ σ
          → Γ prefix-at suc k of Γ,σ,Δ
          → R.weaken-τ-k (suc k) σ ∈ Γ,σ,Δ at ctx-idx k
          → Γ,σ,Δ ok
          → ([ ℓ ↦Γ ε ] Γ,σ,Δ) ok
  sub-Γok {k = zero}  _  _                            _   (TCTX-Bind Γ,σ,Δok τδ) = Γ,σ,Δok
  sub-Γok {k = suc _} εδ (prefix-cons Γ-prefix-Γ,σ,Δ) σ-∈ (TCTX-Bind Γ,σ,Δok τδ)
      = TCTX-Bind (sub-Γok εδ Γ-prefix-Γ,σ,Δ (∈-chop (∈-sucify σ-∈)) Γ,σ,Δok) (sub-Γ⊢τ εδ Γ-prefix-Γ,σ,Δ (∈-chop (∈-sucify σ-∈)) τδ)

  -- Referred to as sub-TWF in the paper
  sub-Γ⊢τ : ∀ {k} {Γ : Ctx ℓ} {Γ,σ,Δ : Ctx (suc k + ℓ)} {τ : SType (suc k + ℓ)}
          → Γ ⊢ ε ⦂ σ
          → Γ prefix-at suc k of Γ,σ,Δ
          → R.weaken-τ-k (suc k) σ ∈ Γ,σ,Δ at ctx-idx k
          → Γ,σ,Δ ⊢ τ
          → [ ℓ ↦Γ ε ] Γ,σ,Δ ⊢ [ ℓ ↦τ< ε ] τ
  sub-Γ⊢τ εδ prefix σ-∈ (TWF-TrueRef Γok) = TWF-TrueRef (sub-Γok εδ prefix σ-∈ Γok)
  sub-Γ⊢τ {ε = ε} {k = k} εδ prefix σ-∈ (TWF-Base {ε₁ = ε₁} {ε₂ = ε₂} ε₁δ ε₂δ)
    rewrite S.act-ε-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) ε₁
          | S.act-ε-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) ε₂
          | R.act-ε-distr (raise k) suc ε
          = let σ-∈' = ∈-suc (weaken-τ-suc-k _ _) σ-∈
                ε₁δ' = sub-Γ⊢ε⦂τ εδ (prefix-cons prefix) σ-∈' ε₁δ
                ε₂δ' = sub-Γ⊢ε⦂τ εδ (prefix-cons prefix) σ-∈' ε₂δ
             in TWF-Base ε₁δ' ε₂δ'
  sub-Γ⊢τ εδ prefix σ-∈ (TWF-Conj ρ₁δ ρ₂δ) = TWF-Conj (sub-Γ⊢τ εδ prefix σ-∈ ρ₁δ) (sub-Γ⊢τ εδ prefix σ-∈ ρ₂δ)
  sub-Γ⊢τ {ε = ε} {k = k} εδ prefix σ-∈ (TWF-Arr {τ₂ = τ₂} arrδ resδ)
    rewrite S.act-τ-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) τ₂
          | R.act-ε-distr (raise k) suc ε
          = TWF-Arr (sub-Γ⊢τ εδ prefix σ-∈ arrδ) (sub-Γ⊢τ εδ (prefix-cons prefix) (∈-suc (weaken-τ-suc-k _ _) σ-∈) resδ)
  sub-Γ⊢τ {ℓ = ℓ} {ε = ε} {σ = σ} {k = k} {Γ = Γ} {Γ,σ,Δ = Γ,σ,Δ} εδ prefix σ-∈ (TWF-ADT consδs) = TWF-ADT (sub-cons consδs)
    where
      sub-cons : ∀ {cons : ADTCons nₐ _}
               → All (λ conτ → Γ,σ,Δ ⊢ conτ) cons
               → All (λ conτ → [ ℓ ↦Γ ε ] Γ,σ,Δ ⊢ conτ) ([ ctx-idx k ↦c R.weaken-ε-k k ε ] cons)
      sub-cons [] = []
      sub-cons (px ∷ pxs) = sub-Γ⊢τ εδ prefix σ-∈ px ∷ sub-cons pxs

  sub-Γ⊢ε⦂τ : ∀ {k} {Γ : Ctx ℓ} {Γ,σ,Δ : Ctx (suc k + ℓ)} {ε₀ : STerm (suc k + ℓ)} {τ : SType (suc k + ℓ)}
            → Γ ⊢ ε ⦂ σ
            → Γ prefix-at suc k of Γ,σ,Δ
            → R.weaken-τ-k (suc k) σ ∈ Γ,σ,Δ at ctx-idx k
            → Γ,σ,Δ ⊢ ε₀ ⦂ τ
            → [ ℓ ↦Γ ε ] Γ,σ,Δ ⊢ [ ℓ ↦ε< ε ] ε₀ ⦂ [ ℓ ↦τ< ε ] τ
  sub-Γ⊢ε⦂τ εδ prefix σ-∈ (T-Unit Γok) = T-Unit (sub-Γok εδ prefix σ-∈ Γok)
  sub-Γ⊢ε⦂τ {ε = ε} {σ = σ} {k = k} εδ prefix σ-∈ (T-Var {idx = idx} Γok τ-∈) with ctx-idx k <>? idx
  ... | less rep<var = T-Var (sub-Γok εδ prefix σ-∈ Γok) (var-earlier-in-Γ-remains ε τ-∈ rep<var)
  ... | equal refl rewrite ∈-injective τ-∈ σ-∈
                         | replace-weakened-τ k (weaken-ε-k k ε) σ
                         = t-weakening-prefix (prefix-subst prefix) (sub-Γok εδ prefix σ-∈ Γok) εδ
  ... | greater rep>var = T-Var (sub-Γok εδ prefix σ-∈ Γok) (var-later-in-Γ-remains ε τ-∈ rep>var)
  sub-Γ⊢ε⦂τ {ℓ = ℓ} {ε = ε} {k = k} {Γ,σ,Δ = Γ,σ,Δ} εδ prefix σ-∈ (T-Abs {τ₁ = τ₁} {τ₂ = τ₂} {ε = ε'} arrδ bodyδ)
    = T-Abs (sub-Γ⊢τ εδ prefix σ-∈ arrδ) bodyδ'
    where
      bodyδ' : [ ℓ ↦Γ ε ] (Γ,σ,Δ , τ₁) ⊢
               S.act-ε (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) ε' ⦂
               S.act-τ (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) τ₂
      bodyδ' rewrite S.act-τ-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) τ₂
                   | S.act-ε-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) ε'
                   | R.act-ε-distr (raise k) suc ε
                   = sub-Γ⊢ε⦂τ εδ (prefix-cons prefix) (∈-suc (weaken-τ-suc-k _ _) σ-∈) bodyδ
  sub-Γ⊢ε⦂τ {ℓ = ℓ} {ε = ε} {k = k} {Γ,σ,Δ = Γ,σ,Δ} εδ prefix σ-∈ (T-App {ε₁ = ε₁} {τ₁} {τ₂} {ε₂} ε₁δ ε₂δ)
    rewrite subst-commutes-τ (ctx-idx k) (R.weaken-ε-k _ ε) ε₂ τ₂
          = T-App ε₁δ' (sub-Γ⊢ε⦂τ εδ prefix σ-∈ ε₂δ)
    where
      ε₁δ' : [ ℓ ↦Γ ε ] Γ,σ,Δ ⊢ [ ctx-idx k ↦ε R.weaken-ε-k k ε ] ε₁ ⦂ ([ ctx-idx k ↦τ R.weaken-ε-k k ε ] τ₁) ⇒
                                                                       ([ ctx-idx (suc k) ↦τ R.weaken-ε (R.weaken-ε-k k ε) ] τ₂)
      ε₁δ' rewrite sym (S.act-τ-extensionality (ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) τ₂) = sub-Γ⊢ε⦂τ εδ prefix σ-∈ ε₁δ
  sub-Γ⊢ε⦂τ {ℓ = ℓ} {ε = ε} {k = k} {Γ,σ,Δ = Γ,σ,Δ} εδ prefix σ-∈ (T-Case resδ ε₀δ branches)
    = T-Case (sub-Γ⊢τ εδ prefix σ-∈ resδ) (sub-Γ⊢ε⦂τ εδ prefix σ-∈ ε₀δ) (sub-branches branches)
    where
      sub-branches : ∀ {bs : CaseBranches nₐ (suc k + ℓ)} {cons : ADTCons nₐ (suc k + ℓ)}
                   → BranchesHaveType Γ,σ,Δ cons bs τ
                   → BranchesHaveType ([ ℓ ↦Γ ε ] Γ,σ,Δ) ([ ℓ ↦c< ε ] cons) ([ ℓ ↦bs< ε ] bs) ([ ℓ ↦τ< ε ] τ)
      sub-branches NoBranches = NoBranches
      sub-branches {τ = τ} (OneMoreBranch {ε' = ε'} {conτ = conτ} branch-εδ bs) = OneMoreBranch branch-εδ' (sub-branches bs)
        where
          branch-εδ' : [ ℓ ↦Γ ε ] (Γ,σ,Δ , conτ) ⊢ S.act-ε (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) ε' ⦂ weaken-τ ([ ℓ ↦τ< ε ] τ)
          branch-εδ' rewrite R.weaken-ε-suc-k k ε
                           | weaken-↦<-τ-comm (ctx-idx k) (R.weaken-ε-k _ ε) τ
                           | S.act-ε-extensionality (ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) ε'
                           | R.act-ε-distr (raise k) suc ε
                           = sub-Γ⊢ε⦂τ εδ (prefix-cons prefix) (∈-suc (weaken-τ-suc-k _ _) σ-∈) branch-εδ
  sub-Γ⊢ε⦂τ εδ prefix σ-∈ (T-Con {cons = cons} ≡-prf conδ adtτ)
    = T-Con (S.act-cons-member _ cons ≡-prf) (sub-Γ⊢ε⦂τ εδ prefix σ-∈ conδ) (sub-Γ⊢τ εδ prefix σ-∈ adtτ)
  sub-Γ⊢ε⦂τ εδ prefix σ-∈ (T-Sub ε₀δ superδ <:δ) = T-Sub
                                                    (sub-Γ⊢ε⦂τ εδ prefix σ-∈ ε₀δ)
                                                    (sub-Γ⊢τ εδ prefix σ-∈ superδ)
                                                    (sub-Γ⊢τ<:τ' εδ prefix σ-∈ <:δ)

  sub-Γ⊢τ<:τ' : ∀ {k} {Γ : Ctx ℓ} {Γ,σ,Δ : Ctx (suc k + ℓ)} {τ τ' : SType (suc k + ℓ)}
              → Γ ⊢ ε ⦂ σ
              → Γ prefix-at suc k of Γ,σ,Δ
              → R.weaken-τ-k (suc k) σ ∈ Γ,σ,Δ at ctx-idx k
              → Γ,σ,Δ ⊢ τ <: τ'
              → [ ℓ ↦Γ ε ] Γ,σ,Δ ⊢ [ ℓ ↦τ< ε ] τ <: [ ℓ ↦τ< ε ] τ'
  sub-Γ⊢τ<:τ' εδ prefix σ-∈ (ST-Base oracle x) = ST-Base oracle (Oracle.subst oracle prefix σ-∈ x)
  sub-Γ⊢τ<:τ' {ℓ = ℓ} {ε = ε} {k = k} {Γ,σ,Δ = Γ,σ,Δ} εδ prefix σ-∈ (ST-Arr {τ₁' = τ₁'} {τ₂ = τ₂} {τ₂' = τ₂'} <:₁ <:₂)
    = ST-Arr (sub-Γ⊢τ<:τ' εδ prefix σ-∈ <:₁) <:₂'
    where
      <:₂' : [ ℓ ↦Γ ε ] (Γ,σ,Δ , τ₁') ⊢ S.act-τ (S.ext (replace-at (ctx-idx k) (weaken-ε-k k ε))) τ₂ <: S.act-τ (S.ext (replace-at (ctx-idx k) (weaken-ε-k k ε))) τ₂'
      <:₂' rewrite S.act-τ-extensionality (ext-replace-comm (weaken-ε-k k ε) (ctx-idx k)) τ₂
                 | S.act-τ-extensionality (ext-replace-comm (weaken-ε-k k ε) (ctx-idx k)) τ₂'
                 | R.act-ε-distr (raise k) suc ε
                 = sub-Γ⊢τ<:τ' εδ (prefix-cons prefix) (∈-suc (weaken-τ-suc-k _ _) σ-∈) <:₂

sub-Γ⊢ε⦂τ-front : ∀ {Γ : Ctx ℓ}
                → Γ ⊢ ϖ ⦂ σ
                → Γ , σ ⊢ ε ⦂ τ
                → Γ ⊢ [ zero ↦ε ϖ ] ε ⦂ [ zero ↦τ ϖ ] τ
sub-Γ⊢ε⦂τ-front {ℓ = ℓ} {ϖ = ϖ} {ε = ε} {τ = τ} {Γ = Γ} ϖδ εδ = prf'
  where
    prf : Γ ⊢ [ ℓ ↦ε< ϖ ] ε ⦂ ([ ℓ ↦τ< ϖ ] τ)
    prf = sub-Γ⊢ε⦂τ ϖδ (prefix-cons prefix-refl) (∈-zero refl) εδ
    prf' : Γ ⊢ [ zero ↦ε ϖ ] ε ⦂ [ zero ↦τ ϖ ] τ
    prf' rewrite sym (act-ε-id (λ _ → refl) ϖ) = prf

sub-Γ⊢τ-front : ∀ {Γ : Ctx ℓ}
              → Γ ⊢ ε ⦂ σ
              → Γ , σ ⊢ τ
              → Γ ⊢ [ zero ↦τ ε ] τ
sub-Γ⊢τ-front {ℓ = ℓ} {ε = ε} {τ = τ} {Γ = Γ} εδ τδ = prf'
  where
    prf : Γ ⊢ [ ℓ ↦τ< ε ] τ
    prf = sub-Γ⊢τ εδ (prefix-cons prefix-refl) (∈-zero refl) τδ
    prf' : Γ ⊢ [ zero ↦τ ε ] τ
    prf' rewrite sym (R.act-ε-id (λ _ → refl) ε) = prf
