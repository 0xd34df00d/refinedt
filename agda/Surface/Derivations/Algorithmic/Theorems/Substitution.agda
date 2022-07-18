{-# OPTIONS --allow-unsolved-metas #-}

module Surface.Derivations.Algorithmic.Theorems.Substitution where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (suc; zero; fromℕ<; raise)
open import Data.Nat.Base using (suc; zero; _+_)
open import Data.Nat.Properties using (≤-stepsʳ; ≤-refl; m≢1+n+m; suc-injective)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
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
open import Surface.Derivations.Algorithmic.Theorems.Thinning
open import Surface.Derivations.Algorithmic.Theorems.Subtyping

sub-Γ⊢τ'<:τ : (εδ : Γ ⊢[ θ , φ of t-sub ] ε ⦂ σ)
            → (Δ : ,-CtxSuffix ℓ σ k)
            → Γ ,σ, Δ ⊢[ θ ] τ' <: τ
            → Γ ++ [↦Δ ε ] Δ ⊢[ θ ] [ ℓ ↦τ< ε ] τ' <: [ ℓ ↦τ< ε ] τ
sub-Γ⊢τ'<:τ {θ = θ} εδ Δ (ST-Base is-just) = ST-Base (Oracle.subst {- TODO εδ -} θ is-just)
sub-Γ⊢τ'<:τ {ε = ε} {k = k} εδ Δ (ST-Arr {τ₂' = τ₂'} {τ₂ = τ₂} <:₁δ <:₂δ)
  rewrite S.act-τ-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) τ₂
        | S.act-τ-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) τ₂'
        | R.act-ε-distr (raise k) suc ε
        = ST-Arr (sub-Γ⊢τ'<:τ εδ Δ <:₁δ) (sub-Γ⊢τ'<:τ εδ (Δ , _) <:₂δ)
sub-Γ⊢τ'<:τ εδ Δ ST-ADT = ST-ADT

sub-Γ⊢τ'<:τ-front : (εδ : Γ ⊢[ θ , φ of t-sub ] ε ⦂ σ)
                  → Γ , σ ⊢[ θ ] τ' <: τ
                  → Γ ⊢[ θ ] [ zero ↦τ ε ] τ' <: [ zero ↦τ ε ] τ
sub-Γ⊢τ'<:τ-front {ε = ε} εδ <:δ
  with <:δ' ← sub-Γ⊢τ'<:τ εδ [ _ ] <:δ
  rewrite R.act-ε-id (λ _ → refl) ε
        = <:δ'

module M {σ : SType ℓ} (εδ : Γ ⊢[ θ , φ of t-sub ] ε ⦂ σ) where mutual
  sub-Γok : (Δ : ,-CtxSuffix ℓ σ k)
          → (Γ ,σ, Δ) ok[ θ , φ ]
          → (Γ ++ [↦Δ ε ] Δ) ok[ θ , φ ]
  sub-Γok [ _ ] (TCTX-Bind Γ-ok _) = Γ-ok
  sub-Γok (Δ , τ) (TCTX-Bind Γ,σ,Δ-ok τδ) = TCTX-Bind (sub-Γok Δ Γ,σ,Δ-ok) (sub-Γ⊢τ Δ τδ)

  sub-Γ⊢τ : (Δ : ,-CtxSuffix ℓ σ k)
          → Γ ,σ, Δ ⊢[ θ , φ ] τ
          → Γ ++ [↦Δ ε ] Δ ⊢[ θ , φ ] [ ℓ ↦τ< ε ] τ
  sub-Γ⊢τ Δ (TWF-TrueRef Γok) = TWF-TrueRef (sub-Γok Δ Γok)
  sub-Γ⊢τ {k = k} Δ (TWF-Base {ε₁ = ε₁} {ε₂ = ε₂} ε₁δ ε₂δ)
    rewrite S.act-ε-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) ε₁
          | S.act-ε-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) ε₂
          | R.act-ε-distr (raise k) suc ε
          = TWF-Base (as-sub (sub-Γ⊢ε⦂τ (Δ , _) ε₁δ)) (as-sub (sub-Γ⊢ε⦂τ (Δ , _) ε₂δ))
  sub-Γ⊢τ Δ (TWF-Conj τ₁δ τ₂δ) = TWF-Conj (sub-Γ⊢τ Δ τ₁δ) (sub-Γ⊢τ Δ τ₂δ)
  sub-Γ⊢τ {k = k} Δ (TWF-Arr {τ₂ = τ₂} τ₁δ τ₂δ)
    rewrite S.act-τ-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) τ₂
          | R.act-ε-distr (raise k) suc ε
          = TWF-Arr (sub-Γ⊢τ Δ τ₁δ) (sub-Γ⊢τ (Δ , _) τ₂δ)
  sub-Γ⊢τ Δ (TWF-ADT consδs) = TWF-ADT (sub-cons Δ consδs)

  sub-cons : {cons : ADTCons nₐ _}
           → (Δ : ,-CtxSuffix ℓ σ k)
           → All (λ conτ → Γ ,σ, Δ ⊢[ θ , φ ] conτ) cons
           → All (λ conτ → Γ ++ [↦Δ ε ] Δ ⊢[ θ , φ ] conτ) ([ ctx-idx k ↦c R.weaken-ε-k k ε ] cons)
  sub-cons Δ [] = []
  sub-cons Δ (τδ ∷ τδs) = sub-Γ⊢τ Δ τδ ∷ sub-cons Δ τδs

  sub-Γ⊢ε⦂τ : (Δ : ,-CtxSuffix ℓ σ k)
            → Γ ,σ, Δ ⊢[ θ , φ of κ ] ε₀ ⦂ τ
            → ∃[ κ' ] (Γ ++ [↦Δ ε ] Δ ⊢[ θ , φ of κ' ] [ ℓ ↦ε< ε ] ε₀ ⦂ [ ℓ ↦τ< ε ] τ)
  sub-Γ⊢ε⦂τ Δ (T-Unit Γok) = ⟨ _ , T-Unit (sub-Γok Δ Γok) ⟩
  sub-Γ⊢ε⦂τ {k = k} Δ (T-Var {ι = ι} Γok ∈) with ctx-idx k <>? ι
  ... | less k<ι = ⟨ _ , T-Var (sub-Γok Δ Γok) (var-earlier-in-Γ-remains Δ ∈ k<ι) ⟩
  ... | equal refl rewrite ∈-at-concat-point Δ ∈
                         | replace-weakened-τ k (weaken-ε-k k ε) σ
                         = ⟨ t-sub , Γ⊢ε⦂τ-weakening-suffix (sub-Γok Δ Γok) εδ ⟩
  ... | greater k>ι = ⟨ _ , T-Var (sub-Γok Δ Γok) (var-later-in-Γ-remains Δ ∈ k>ι) ⟩
  sub-Γ⊢ε⦂τ Δ (T-Abs arrδ δ) = {! !}
  sub-Γ⊢ε⦂τ Δ (T-App δ δ₁ resτ-≡ resτδ) = {! !}
  sub-Γ⊢ε⦂τ Δ (T-Case resδ δ branches-well-typed) = {! !}
  sub-Γ⊢ε⦂τ Δ (T-Con ≡-prf δ adtτ) = {! !}
  sub-Γ⊢ε⦂τ Δ (T-Sub δ τδ <:δ) = {! !}
  {-
  It seems to be impossible to prove the substitution lemma directly for the enriched type system.

  Both systems require transitivity of subtyping relations to collapse
  any possible nested T-Sub rules after the substitution. In turn,
  transitivity of subtyping relations for ST-Arr requires narrowing of the
  "higher" relation, which, in case of the enriched system, also pulls in
  narrowing for the type well-formedness witnesses that it carries.
  -}

open M public

sub-Γ⊢τ-front : {Γ : Ctx ℓ}
              → Γ ⊢[ θ , φ of t-sub ] ε ⦂ σ
              → Γ , σ ⊢[ θ , φ ] τ
              → Γ ⊢[ θ , φ ] [ zero ↦τ ε ] τ
sub-Γ⊢τ-front {ε = ε} εδ τδ
  with τδ' ← sub-Γ⊢τ εδ [ _ ] τδ
  rewrite R.act-ε-id (λ _ → refl) ε
        = τδ'
