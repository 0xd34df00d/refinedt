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
open import Surface.WellScoped.Substitution using ([_↦τ_]_; [_↦ε_]_; [_↦c_]_)
open import Surface.WellScoped.Membership
open import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.Substitution as S
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

-- It's interesting to note that _⊂_ does not work as nicely to express the notion of a prefix of a context.
-- Indeed, the information that the last element of the supercontext can be chopped off is lost:
-- _⊂_ can also imply that arbitrary bindings are inserted in the middle of the context, not necessarily appended to it.
-- We could have used _⊂_ with an extra requirement that ρ : Fin ℓ → Fin ℓ' is such that ∀ x → toℕ x ≡ toℕ (ρ x),
-- but it gets super messy really soon. For example, even proving that if ℓ' ≠ ℓ,
-- then extra elements were appended to the supercontext, is non-trivial.
-- It's perhaps cleanest and cheapest to just add an extra predicate.

infix 3 _prefix-at_of_
data _prefix-at_of_ : (Γ : Ctx ℓ) → (k : ℕ) → (Γ' : Ctx (k + ℓ)) → Set where
  prefix-refl : Γ prefix-at zero of Γ
  prefix-cons : ∀ {k} {Γ : Ctx ℓ} {Γ' : Ctx (k + ℓ)} {τ : SType (k + ℓ)}
              → Γ prefix-at k of Γ'
              → Γ prefix-at (suc k) of (Γ' , τ)

-- Some local helpers

τ∈Γ-⇒-Γ⊢τ : Γ ok → τ ∈ Γ at ι → Γ ⊢ τ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind δ τδ) ∈-zero = twf-weakening δ τδ τδ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind δ τδ) (∈-suc ∈) = twf-weakening δ τδ (τ∈Γ-⇒-Γ⊢τ δ ∈)

prefix-subst : ∀ {k} {Γ : Ctx ℓ} {Γ' : Ctx (suc k + ℓ)}
             → Γ prefix-at suc k of Γ'
             → Γ prefix-at k of ([ ℓ ↦Γ ε ] Γ')
prefix-subst {k = zero} (prefix-cons prefix) = prefix
prefix-subst {k = suc k} (prefix-cons prefix) = prefix-cons (prefix-subst prefix)


[_↦τ<_]_ : ∀ {k} ℓ
         → (ε : STerm ℓ) → SType (suc k + ℓ) → SType (k + ℓ)
[_↦τ<_]_ {k = k} _ ε τ = [ ctx-idx k ↦τ R.weaken-ε-k _ ε ] τ

[_↦ε<_]_ : ∀ {k} ℓ
         → (ε : STerm ℓ) → STerm (suc k + ℓ) → STerm (k + ℓ)
[_↦ε<_]_ {k = k} _ ε ε' = [ ctx-idx k ↦ε R.weaken-ε-k _ ε ] ε'

prefix-∈-≡ : ∀ {k} {Γ : Ctx ℓ} {Γ,σ,Δ : Ctx (suc k + ℓ)} {τ : SType (suc k + ℓ)}
           → Γ prefix-at suc k of Γ,σ,Δ
           → τ ∈ Γ,σ,Δ at ctx-idx k
           → τ ≡ weaken-τ-k (suc k) σ
prefix-∈-≡ {k = zero} prefix ∈ = {! !}
prefix-∈-≡ {k = suc k} prefix ∈ = {! !}

mutual
  sub-Γok : ∀ {k} {Γ : Ctx ℓ} {Γ,σ,Δ : Ctx (suc k + ℓ)}
          → Γ ⊢ ε ⦂ σ
          → Γ prefix-at suc k of Γ,σ,Δ
          → Γ,σ,Δ ok
          → ([ ℓ ↦Γ ε ] Γ,σ,Δ) ok
  sub-Γok {k = zero}  _  _                            (TCTX-Bind Γ,σ,Δok τδ) = Γ,σ,Δok
  sub-Γok {k = suc _} εδ (prefix-cons Γ-prefix-Γ,σ,Δ) (TCTX-Bind Γ,σ,Δok τδ) =
      TCTX-Bind (sub-Γok εδ Γ-prefix-Γ,σ,Δ Γ,σ,Δok) (sub-Γ⊢τ εδ Γ-prefix-Γ,σ,Δ τδ)

  sub-Γ⊢τ : ∀ {k} {Γ : Ctx ℓ} {Γ,σ,Δ : Ctx (suc k + ℓ)} {τ : SType (suc k + ℓ)}
          → Γ ⊢ ε ⦂ σ
          → Γ prefix-at suc k of Γ,σ,Δ
          → Γ,σ,Δ ⊢ τ
          → [ ℓ ↦Γ ε ] Γ,σ,Δ ⊢ [ ℓ ↦τ< ε ] τ
  sub-Γ⊢τ εδ prefix (TWF-TrueRef Γok) = TWF-TrueRef (sub-Γok εδ prefix Γok)
  sub-Γ⊢τ {ε = ε} {k = k} εδ prefix (TWF-Base {ε₁ = ε₁} {ε₂ = ε₂} ε₁δ ε₂δ)
    rewrite S.act-ε-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) ε₁
          | S.act-ε-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) ε₂
          = TWF-Base (sub-Γ⊢ε⦂τ εδ (prefix-cons prefix) ε₁δ) (sub-Γ⊢ε⦂τ εδ (prefix-cons prefix) ε₂δ)
  sub-Γ⊢τ εδ prefix (TWF-Conj ρ₁δ ρ₂δ) = TWF-Conj (sub-Γ⊢τ εδ prefix ρ₁δ) (sub-Γ⊢τ εδ prefix ρ₂δ)
  sub-Γ⊢τ {ε = ε} {k = k} εδ prefix (TWF-Arr {τ₂ = τ₂} arrδ resδ)
      rewrite S.act-τ-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) τ₂ =
          TWF-Arr (sub-Γ⊢τ εδ prefix arrδ) (sub-Γ⊢τ εδ (prefix-cons prefix) resδ)
  sub-Γ⊢τ {ℓ = ℓ} {ε = ε} {σ = σ} {k = k} {Γ = Γ} {Γ,σ,Δ = Γ,σ,Δ} εδ prefix (TWF-ADT consδs) = TWF-ADT (sub-cons consδs)
    where
      sub-cons : ∀ {cons : ADTCons nₐ _}
               → All (λ conτ → Γ,σ,Δ ⊢ conτ) cons
               → All (λ conτ → [ ℓ ↦Γ ε ] Γ,σ,Δ ⊢ conτ) ([ ctx-idx k ↦c R.weaken-ε-k k ε ] cons)
      sub-cons [] = []
      sub-cons (px ∷ pxs) = sub-Γ⊢τ εδ prefix px ∷ sub-cons pxs

  sub-Γ⊢τ-front : Γ ⊢ ε ⦂ σ
                → Γ , σ ⊢ τ
                → Γ ⊢ [ zero ↦τ ε ] τ
  sub-Γ⊢τ-front εδ τδ = sub-Γ⊢τ εδ (prefix-cons prefix-refl) τδ

  sub-Γ⊢ε⦂τ : ∀ {k} {Γ : Ctx ℓ} {Γ,σ,Δ : Ctx (suc (k + ℓ))} {ε₀ : STerm (suc k + ℓ)} {τ : SType (suc k + ℓ)}
            → Γ ⊢ ε ⦂ σ
            → Γ prefix-at suc k of Γ,σ,Δ
            → Γ,σ,Δ ⊢ ε₀ ⦂ τ
            → [ ℓ ↦Γ ε ] Γ,σ,Δ ⊢ [ ℓ ↦ε< ε ] ε₀ ⦂ [ ℓ ↦τ< ε ] τ
  sub-Γ⊢ε⦂τ εδ prefix (T-Unit Γok) = T-Unit (sub-Γok εδ prefix Γok)
  sub-Γ⊢ε⦂τ {k = k} εδ prefix (T-Var {idx = idx} Γok x) with ctx-idx k <>? idx
  ... | less rep<var = T-Var (sub-Γok εδ prefix Γok) {! !}
  ... | equal = {! !}
  ... | greater rep>var = T-Var (sub-Γok εδ prefix Γok) {! !}
  sub-Γ⊢ε⦂τ {ℓ = ℓ} {ε = ε} {k = k} {Γ,σ,Δ = Γ,σ,Δ} εδ prefix (T-Abs {τ₁ = τ₁} {τ₂ = τ₂} {ε = ε'} arrδ bodyδ)
    = T-Abs (sub-Γ⊢τ εδ prefix arrδ) bodyδ'
    where
      bodyδ' :   [ ℓ ↦Γ ε ] (Γ,σ,Δ , τ₁)
               ⊢ S.act-ε (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) ε'
               ⦂ S.act-τ (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) τ₂
      bodyδ' rewrite S.act-τ-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) τ₂
                   | S.act-ε-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) ε'
                   = sub-Γ⊢ε⦂τ εδ (prefix-cons prefix) bodyδ
  sub-Γ⊢ε⦂τ εδ prefix (T-App ε₁δ ε₂δ) = {! !}
  sub-Γ⊢ε⦂τ εδ prefix (T-Case resδ ε₀δ branches) = {! !}
  sub-Γ⊢ε⦂τ εδ prefix (T-Con conδ adtτ) = {! !}
  sub-Γ⊢ε⦂τ εδ prefix (T-Sub ε₀δ superδ <:δ) = {! !}


Γ⊢ε⦂τ-⇒-Γ⊢τ : Γ ⊢ ε ⦂ τ
            → Γ ⊢ τ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Unit gok) = TWF-TrueRef gok
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Var gok ∈-prf) = τ∈Γ-⇒-Γ⊢τ gok ∈-prf
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Abs arrδ _) = arrδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-App δ₁ δ₂) = sub-Γ⊢τ-front δ₂ (arr-wf-⇒-cod-wf (Γ⊢ε⦂τ-⇒-Γ⊢τ δ₁))
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Case resδ _ _) = resδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Con _ adtτ) = adtτ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Sub δ superδ sub) = superδ
