{-# OPTIONS --safe #-}

module Surface.Theorems where

open import Agda.Builtin.Equality
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (suc; zero; fromℕ<)
open import Data.Nat.Base using (suc; zero; _+_)
open import Data.Nat.Properties using (≤-stepsʳ; ≤-refl; m≢1+n+m)
open import Data.Product renaming (_,_ to _,'_)

open import Data.Fin.Extra
open import Surface.WellScoped
open import Surface.WellScoped.Substitution using ([_↦τ_]_; [_↦ε_]_; [_↦c_]_)
open import Surface.WellScoped.Membership
open import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.Substitution as S
open import Surface.Substitutions
open import Surface.Derivations
open import Surface.Derivations.WF
open import Surface.Theorems.TCTX
open import Surface.Theorems.Helpers
open import Surface.Theorems.Thinning

-- TODO cleanup these modules
-- open import Misc.ContextConcat
-- open import Misc.Helpers
-- open import Misc.SnocList

-- Some local helpers

τ∈Γ-⇒-Γ⊢τ : Γ ok → τ ∈ Γ at ι → Γ ⊢ τ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind δ τδ) ∈-zero = twf-weakening δ τδ τδ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind δ τδ) (∈-suc ∈) = twf-weakening δ τδ (τ∈Γ-⇒-Γ⊢τ δ ∈)

ctx-idx : ∀ k → Fin (suc (k + ℓ))
ctx-idx zero = zero
ctx-idx (suc k) = suc (ctx-idx k)

-- Substitution on contexts: this is essentially replacing Γ, x ⦂ σ, Δ with Γ, [ x ↦ ε ] Δ
-- Here, ℓ is the length of Γ (which ε must live in), and k is the length of Δ.
[_↦Γ_]_ : ∀ {k} ℓ {ℓ'} ⦃ ℓ'-eq : ℓ' ≡ suc (k + ℓ) ⦄
        → (ε : STerm ℓ)
        → Ctx ℓ'
        → Ctx (k + ℓ)
[_↦Γ_]_ {k = zero} ℓ ⦃ ℓ'-eq = refl ⦄ ε (Γ , _) = Γ
[_↦Γ_]_ {k = suc k} ℓ ⦃ ℓ'-eq = refl ⦄ ε (Γ,Δ , τ) = ([ ℓ ↦Γ ε ] Γ,Δ) , ([ ctx-idx k ↦τ R.weaken-ε-k k ε ] τ)

-- Substitution lemmas

-- It's interesting to note that _⊂_ does not work as nicely to express the notion of a prefix of a context.
-- Indeed, the information that the last element of the supercontext can be chopped off is lost:
-- _⊂_ can also imply that arbitrary bindings are inserted in the middle of the context, not necessarily appended to it.
-- We could have used _⊂_ with an extra requirement that ρ : Fin ℓ → Fin ℓ' is such that ∀ x → toℕ x ≡ toℕ (ρ x),
-- but it gets super messy really soon. For example, even proving that if ℓ' ≠ ℓ,
-- then extra elements were appended to the supercontext, is non-trivial.
-- It's perhaps cleanest and cheapest to just add an extra predicate.

infix 3 _is-prefix-of_
data _is-prefix-of_ : (Γ : Ctx ℓ) → (Γ' : Ctx ℓ') → Set where
  prefix-refl : Γ is-prefix-of Γ
  prefix-cons : Γ is-prefix-of Γ'
              → Γ is-prefix-of Γ' , τ

prefix-subst : ∀ {k} {Γ : Ctx ℓ} {Γ' : Ctx ℓ'}
             → Γ is-prefix-of Γ'
             → ⦃ ℓ'-eq : ℓ' ≡ suc (k + ℓ) ⦄
             → Γ is-prefix-of ([ ℓ ↦Γ ε ] Γ')
prefix-subst {k = zero} (prefix-cons prefix) ⦃ ℓ'-eq = refl ⦄ = prefix
prefix-subst {k = suc k} prefix-refl ⦃ ℓ'-eq ⦄ = ⊥-elim (m≢1+n+m _ ℓ'-eq)
prefix-subst {k = suc k} (prefix-cons prefix) ⦃ ℓ'-eq = refl ⦄ = prefix-cons (prefix-subst prefix)


[_↦τ<_]_ : ∀ {k ℓ'} ℓ ⦃ ℓ'-eq : ℓ' ≡ suc (k + ℓ) ⦄
         → (ε : STerm ℓ) → SType ℓ' → SType (k + ℓ)
[_↦τ<_]_ {k = k} _ ⦃ ℓ'-eq = refl ⦄ ε τ = [ ctx-idx k ↦τ R.weaken-ε-k _ ε ] τ

[_↦ε<_]_ : ∀ {k ℓ'} ℓ ⦃ ℓ'-eq : ℓ' ≡ suc (k + ℓ) ⦄
         → (ε : STerm ℓ) → STerm ℓ' → STerm (k + ℓ)
[_↦ε<_]_ {k = k} _ ⦃ ℓ'-eq = refl ⦄ ε ε' = [ ctx-idx k ↦ε R.weaken-ε-k _ ε ] ε'

mutual
  sub-Γok : ∀ {k} {Γ : Ctx ℓ} {Γ,σ,Δ : Ctx ℓ'}
          → Γ ⊢ ε ⦂ σ
          → Γ is-prefix-of Γ,σ,Δ
          → ⦃ ℓ'-eq : ℓ' ≡ suc (k + ℓ) ⦄
          → Γ,σ,Δ ok
          → ([ ℓ ↦Γ ε ] Γ,σ,Δ) ok
  sub-Γok {k = suc _} _ prefix-refl ⦃ ℓ'-eq ⦄                          _                      = ⊥-elim (m≢1+n+m _ ℓ'-eq)
  sub-Γok {k = zero}  _  _                            ⦃ ℓ'-eq = refl ⦄ (TCTX-Bind Γ,σ,Δok τδ) = Γ,σ,Δok
  sub-Γok {k = suc _} εδ (prefix-cons Γ-prefix-Γ,σ,Δ) ⦃ ℓ'-eq = refl ⦄ (TCTX-Bind Γ,σ,Δok τδ) =
      TCTX-Bind (sub-Γok εδ Γ-prefix-Γ,σ,Δ Γ,σ,Δok) (sub-Γ⊢τ εδ Γ-prefix-Γ,σ,Δ τδ)

  sub-Γ⊢τ : ∀ {k} {Γ : Ctx ℓ} {Γ,σ,Δ : Ctx ℓ'} {τ : SType ℓ'}
          → Γ ⊢ ε ⦂ σ
          → Γ is-prefix-of Γ,σ,Δ
          → ⦃ ℓ'-eq : ℓ' ≡ suc (k + ℓ) ⦄
          → Γ,σ,Δ ⊢ τ
          → [ ℓ ↦Γ ε ] Γ,σ,Δ ⊢ [ ℓ ↦τ< ε ] τ
  sub-Γ⊢τ εδ prefix ⦃ ℓ'-eq = refl ⦄ (TWF-TrueRef Γok) = TWF-TrueRef (sub-Γok εδ prefix Γok)
  sub-Γ⊢τ εδ prefix ⦃ ℓ'-eq = refl ⦄ (TWF-Base ε₁δ ε₂δ) = {! !}
  sub-Γ⊢τ εδ prefix ⦃ ℓ'-eq = refl ⦄ (TWF-Conj ρ₁δ ρ₂δ) = TWF-Conj (sub-Γ⊢τ εδ prefix ρ₁δ) (sub-Γ⊢τ εδ prefix ρ₂δ)
  sub-Γ⊢τ {ε = ε} {k = k} εδ prefix ⦃ ℓ'-eq = refl ⦄ (TWF-Arr {τ₂ = τ₂} arrδ resδ)
      rewrite S.act-τ-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) τ₂ =
          TWF-Arr (sub-Γ⊢τ εδ prefix arrδ) (sub-Γ⊢τ εδ (prefix-cons prefix) resδ)
  sub-Γ⊢τ {ℓ = ℓ} {ε = ε} {σ = σ} {k = k} {Γ = Γ} {Γ,σ,Δ = Γ,σ,Δ} εδ prefix ⦃ ℓ'-eq = refl ⦄ (TWF-ADT consδs) = TWF-ADT (sub-cons consδs)
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

  sub-Γ⊢ε⦂τ : ∀ {k} {Γ : Ctx ℓ} {Γ,σ,Δ : Ctx ℓ'} {τ : SType ℓ'}
            → Γ ⊢ ε ⦂ σ
            → Γ is-prefix-of Γ,σ,Δ
            → ⦃ ℓ'-eq : ℓ' ≡ suc (k + ℓ) ⦄
            → Γ,σ,Δ ⊢ ε₀ ⦂ τ
            → [ ℓ ↦Γ ε ] Γ,σ,Δ ⊢ [ ℓ ↦ε< ε ] ε₀ ⦂ [ ℓ ↦τ< ε ] τ
  sub-Γ⊢ε⦂τ εδ prefix ⦃ ℓ'-eq = refl ⦄ (T-Unit Γok) = T-Unit (sub-Γok εδ prefix Γok)
  sub-Γ⊢ε⦂τ {k = k} εδ prefix ⦃ ℓ'-eq = refl ⦄ (T-Var {idx = idx} Γok x) with ctx-idx k <>? idx
  ... | less m<n = T-Var (sub-Γok εδ prefix Γok) {! !}
  ... | equal = {! !}
  ... | greater m>n = T-Var (sub-Γok εδ prefix Γok) {! !}
  sub-Γ⊢ε⦂τ {ℓ = ℓ} {ε = ε} {k = k} {Γ,σ,Δ = Γ,σ,Δ} εδ prefix ⦃ ℓ'-eq = refl ⦄ (T-Abs {τ₁ = τ₁} {τ₂ = τ₂} {ε = ε'} arrδ bodyδ)
    = T-Abs (sub-Γ⊢τ εδ prefix arrδ) bodyδ'
    where
      bodyδ' :   [ ℓ ↦Γ ε ] (Γ,σ,Δ , τ₁)
               ⊢ S.act-ε (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) ε'
               ⦂ S.act-τ (S.ext (S.replace-at (ctx-idx k) (R.weaken-ε-k k ε))) τ₂
      bodyδ' rewrite S.act-τ-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) τ₂
                   | S.act-ε-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) ε'
                   = sub-Γ⊢ε⦂τ εδ (prefix-cons prefix) bodyδ
  sub-Γ⊢ε⦂τ εδ prefix ⦃ ℓ'-eq = refl ⦄ (T-App ε₁δ ε₂δ) = {! !}
  sub-Γ⊢ε⦂τ εδ prefix ⦃ ℓ'-eq = refl ⦄ (T-Case resδ ε₀δ branches) = {! !}
  sub-Γ⊢ε⦂τ εδ prefix ⦃ ℓ'-eq = refl ⦄ (T-Con conδ adtτ) = {! !}
  sub-Γ⊢ε⦂τ εδ prefix ⦃ ℓ'-eq = refl ⦄ (T-Sub ε₀δ superδ <:δ) = {! !}


Γ⊢ε⦂τ-⇒-Γ⊢τ : Γ ⊢ ε ⦂ τ
            → Γ ⊢ τ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Unit gok) = TWF-TrueRef gok
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Var gok ∈-prf) = τ∈Γ-⇒-Γ⊢τ gok ∈-prf
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Abs arrδ _) = arrδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-App δ₁ δ₂) = sub-Γ⊢τ-front δ₂ (arr-wf-⇒-cod-wf (Γ⊢ε⦂τ-⇒-Γ⊢τ δ₁))
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Case resδ _ _) = resδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Con _ adtτ) = adtτ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Sub δ superδ sub) = superδ
