{-# OPTIONS --safe #-}

module Surface.Theorems where

open import Agda.Builtin.Equality
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (suc; zero; fromℕ<)
open import Data.Nat.Base using (suc; zero; _+_)
open import Data.Nat.Properties using (≤-stepsʳ; ≤-refl; m≢1+n+m; suc-injective)
open import Data.Product renaming (_,_ to _,'_)

open import Data.Fin.Extra
open import Surface.WellScoped
open import Surface.WellScoped.CtxPrefix
open import Surface.WellScoped.Membership
open import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.Substitution as S
open import Surface.WellScoped.Substitution using ([_↦τ_]_; [_↦ε_]_; [_↦c_]_)
open import Surface.Derivations
open import Surface.Derivations.WF
open import Surface.Theorems.TCTX
open import Surface.Theorems.Helpers
open import Surface.Theorems.Thinning

-- TODO cleanup these modules
-- open import Misc.ContextConcat
-- open import Misc.Helpers
-- open import Misc.SnocList

-- Substitution lemmas

-- Some local helpers

τ∈Γ-⇒-Γ⊢τ : Γ ok → τ ∈ Γ at ι → Γ ⊢ τ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind δ τδ) (∈-zero refl) = twf-weakening δ τδ τδ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind δ τδ) (∈-suc refl ∈) = twf-weakening δ τδ (τ∈Γ-⇒-Γ⊢τ δ ∈)

[_↦τ<_]_ : ∀ {k} ℓ
         → (ε : STerm ℓ) → SType (suc k + ℓ) → SType (k + ℓ)
[_↦τ<_]_ {k = k} _ ε τ = [ ctx-idx k ↦τ R.weaken-ε-k _ ε ] τ

[_↦ε<_]_ : ∀ {k} ℓ
         → (ε : STerm ℓ) → STerm (suc k + ℓ) → STerm (k + ℓ)
[_↦ε<_]_ {k = k} _ ε ε' = [ ctx-idx k ↦ε R.weaken-ε-k _ ε ] ε'

mutual
  sub-Γok : ∀ {k} {Γ : Ctx ℓ} {Γ,σ,Δ : Ctx (suc k + ℓ)}
          → Γ ⊢ ε ⦂ σ
          → Γ prefix-at suc k of Γ,σ,Δ
          → R.weaken-τ-k (suc k) σ ∈ Γ,σ,Δ at ctx-idx k
          → Γ,σ,Δ ok
          → ([ ℓ ↦Γ ε ] Γ,σ,Δ) ok
  sub-Γok {k = zero}  _  _                            _   (TCTX-Bind Γ,σ,Δok τδ) = Γ,σ,Δok
  sub-Γok {k = suc _} εδ (prefix-cons Γ-prefix-Γ,σ,Δ) σ-∈ (TCTX-Bind Γ,σ,Δok τδ)
      = TCTX-Bind (sub-Γok εδ Γ-prefix-Γ,σ,Δ (∈-chop σ-∈) Γ,σ,Δok) (sub-Γ⊢τ εδ Γ-prefix-Γ,σ,Δ (∈-chop σ-∈) τδ)

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
          = TWF-Base (sub-Γ⊢ε⦂τ εδ (prefix-cons prefix) (∈-suc refl σ-∈) ε₁δ) (sub-Γ⊢ε⦂τ εδ (prefix-cons prefix) (∈-suc refl σ-∈) ε₂δ)
  sub-Γ⊢τ εδ prefix σ-∈ (TWF-Conj ρ₁δ ρ₂δ) = TWF-Conj (sub-Γ⊢τ εδ prefix σ-∈ ρ₁δ) (sub-Γ⊢τ εδ prefix σ-∈ ρ₂δ)
  sub-Γ⊢τ {ε = ε} {k = k} εδ prefix σ-∈ (TWF-Arr {τ₂ = τ₂} arrδ resδ)
    rewrite S.act-τ-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) τ₂
          = TWF-Arr (sub-Γ⊢τ εδ prefix σ-∈ arrδ) (sub-Γ⊢τ εδ (prefix-cons prefix) (∈-suc refl σ-∈) resδ)
  sub-Γ⊢τ {ℓ = ℓ} {ε = ε} {σ = σ} {k = k} {Γ = Γ} {Γ,σ,Δ = Γ,σ,Δ} εδ prefix σ-∈ (TWF-ADT consδs) = TWF-ADT (sub-cons consδs)
    where
      sub-cons : ∀ {cons : ADTCons nₐ _}
               → All (λ conτ → Γ,σ,Δ ⊢ conτ) cons
               → All (λ conτ → [ ℓ ↦Γ ε ] Γ,σ,Δ ⊢ conτ) ([ ctx-idx k ↦c R.weaken-ε-k k ε ] cons)
      sub-cons [] = []
      sub-cons (px ∷ pxs) = sub-Γ⊢τ εδ prefix σ-∈ px ∷ sub-cons pxs

  sub-Γ⊢τ-front : Γ ⊢ ε ⦂ σ
                → Γ , σ ⊢ τ
                → Γ ⊢ [ zero ↦τ ε ] τ
  sub-Γ⊢τ-front εδ τδ = sub-Γ⊢τ εδ (prefix-cons prefix-refl) (∈-zero refl) τδ

  sub-Γ⊢ε⦂τ : ∀ {k} {Γ : Ctx ℓ} {Γ,σ,Δ : Ctx (suc (k + ℓ))} {ε₀ : STerm (suc k + ℓ)} {τ : SType (suc k + ℓ)}
            → Γ ⊢ ε ⦂ σ
            → Γ prefix-at suc k of Γ,σ,Δ
            → R.weaken-τ-k (suc k) σ ∈ Γ,σ,Δ at ctx-idx k
            → Γ,σ,Δ ⊢ ε₀ ⦂ τ
            → [ ℓ ↦Γ ε ] Γ,σ,Δ ⊢ [ ℓ ↦ε< ε ] ε₀ ⦂ [ ℓ ↦τ< ε ] τ
  sub-Γ⊢ε⦂τ εδ prefix σ-∈ (T-Unit Γok) = T-Unit (sub-Γok εδ prefix σ-∈ Γok)
  sub-Γ⊢ε⦂τ {k = k} εδ prefix σ-∈ (T-Var {idx = idx} Γok x) with ctx-idx k <>? idx
  ... | less rep<var = T-Var (sub-Γok εδ prefix σ-∈ Γok) {! !}
  ... | equal = {! !}
  ... | greater rep>var = T-Var (sub-Γok εδ prefix σ-∈ Γok) {! !}
  sub-Γ⊢ε⦂τ {ℓ = ℓ} {ε = ε} {k = k} {Γ,σ,Δ = Γ,σ,Δ} εδ prefix σ-∈ (T-Abs {τ₁ = τ₁} {τ₂ = τ₂} {ε = ε'} arrδ bodyδ)
    = T-Abs (sub-Γ⊢τ εδ prefix σ-∈ arrδ) bodyδ'
    where
      bodyδ' :   [ ℓ ↦Γ ε ] (Γ,σ,Δ , τ₁)
               ⊢ S.act-ε (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) ε'
               ⦂ S.act-τ (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) τ₂
      bodyδ' rewrite S.act-τ-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) τ₂
                   | S.act-ε-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) ε'
                   = sub-Γ⊢ε⦂τ εδ (prefix-cons prefix) (∈-suc refl σ-∈) bodyδ
  sub-Γ⊢ε⦂τ εδ prefix σ-∈ (T-App ε₁δ ε₂δ) = {! !}
  sub-Γ⊢ε⦂τ εδ prefix σ-∈ (T-Case resδ ε₀δ branches) = {! !}
  sub-Γ⊢ε⦂τ εδ prefix σ-∈ (T-Con conδ adtτ) = {! !}
  sub-Γ⊢ε⦂τ εδ prefix σ-∈ (T-Sub ε₀δ superδ <:δ) = {! !}


Γ⊢ε⦂τ-⇒-Γ⊢τ : Γ ⊢ ε ⦂ τ
            → Γ ⊢ τ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Unit gok) = TWF-TrueRef gok
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Var gok ∈-prf) = τ∈Γ-⇒-Γ⊢τ gok ∈-prf
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Abs arrδ _) = arrδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-App δ₁ δ₂) = sub-Γ⊢τ-front δ₂ (arr-wf-⇒-cod-wf (Γ⊢ε⦂τ-⇒-Γ⊢τ δ₁))
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Case resδ _ _) = resδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Con _ adtτ) = adtτ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Sub δ superδ sub) = superδ
