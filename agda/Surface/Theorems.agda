{-# OPTIONS --safe #-}

module Surface.Theorems where

open import Agda.Builtin.Equality
open import Data.Bool.Base
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (fromℕ<)
open import Data.Nat.Properties using (≤-stepsʳ; ≤-refl; m≢1+n+m)
open import Data.Product renaming (_,_ to _,'_)

open import Surface.WellScoped
open        Surface.WellScoped.S using ([_↦τ_]_; [_↦c_]_)
open import Surface.Substitutions
open import Surface.Derivations
open import Surface.Derivations.WF
open import Surface.Theorems.TCTX
open import Surface.Theorems.Helpers
open import Surface.Theorems.Thinning

-- TODO cleanup these modules
-- open import Misc.Sublist
-- open import Misc.ContextConcat
-- open import Misc.Helpers
-- open import Misc.SnocList

-- Some local helpers

τ∈Γ-⇒-Γ⊢τ : Γ ok → τ ∈ Γ at ι → Γ ⊢ τ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind δ τδ) ∈-zero = twf-weakening δ τδ τδ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind δ τδ) (∈-suc ∈) = twf-weakening δ τδ (τ∈Γ-⇒-Γ⊢τ δ ∈)

ctx-idx : ∀ {k} ℓ → Fin (suc (k + ℓ))
ctx-idx ℓ = fromℕ< (≤-stepsʳ ℓ ≤-refl)

-- Substitution on contexts: this is essentially replacing Γ, x ⦂ σ, Δ with Γ, [ x ↦ ε ] Δ
-- Here, ℓ is the length of Γ (which ε must live in), and k is the length of Δ.
[_↦Γ_]_ : ∀ {k} ℓ {ℓ'} ⦃ ℓ'-eq : ℓ' ≡ suc (k + ℓ) ⦄
        → (ε : STerm ℓ)
        → Ctx ℓ'
        → Ctx (k + ℓ)
[_↦Γ_]_ {k = zero} ℓ ⦃ ℓ'-eq = refl ⦄ ε (Γ , _) = Γ
[_↦Γ_]_ {k = suc k} ℓ ⦃ ℓ'-eq = refl ⦄ ε (Γ,Δ , τ) = ([ ℓ ↦Γ ε ] Γ,Δ) , ([ ctx-idx ℓ ↦τ R.weaken-ε-k k ε ] τ)

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

[_↦τ<_]_ : ∀ {k ℓ'} ℓ ⦃ ℓ'-eq : ℓ' ≡ suc (k + ℓ) ⦄
         → (ε : STerm ℓ) → SType ℓ' → SType (k + ℓ)
[_↦τ<_]_ ℓ ⦃ ℓ'-eq = refl ⦄ ε τ = [ ctx-idx ℓ ↦τ R.weaken-ε-k _ ε ] τ

mutual
  sub-Γok : ∀ {k} {Γ : Ctx ℓ} {Γ,σ,Δ : Ctx ℓ'}
          → Γ ⊢ ε ⦂ σ
          → Γ is-prefix-of Γ,σ,Δ
          → ⦃ ℓ'-eq : ℓ' ≡ suc (k + ℓ) ⦄
          → Γ,σ,Δ ok
          → ([ ℓ ↦Γ ε ] Γ,σ,Δ) ok
  sub-Γok {ℓ = ℓ} {k = suc _} _ prefix-refl ⦃ ℓ'-eq ⦄ _ = ⊥-elim (m≢1+n+m ℓ ℓ'-eq)
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
  sub-Γ⊢τ εδ prefix ⦃ ℓ'-eq = refl ⦄ (TWF-Arr arrδ resδ) = TWF-Arr (sub-Γ⊢τ εδ prefix arrδ) {! !}
  sub-Γ⊢τ {ℓ = ℓ} {ε = ε} {σ = σ} {k = k} {Γ = Γ} {Γ,σ,Δ = Γ,σ,Δ} εδ prefix ⦃ ℓ'-eq = refl ⦄ (TWF-ADT consδs) = TWF-ADT (sub-cons consδs)
    where
      sub-cons : ∀ {cons : ADTCons nₐ _}
               → All (λ conτ → Γ,σ,Δ ⊢ conτ) cons
               → All (λ conτ → [ ℓ ↦Γ ε ] Γ,σ,Δ ⊢ conτ) ([ ctx-idx ℓ ↦c R.weaken-ε-k k ε ] cons)
      sub-cons [] = []
      sub-cons (px ∷ pxs) = sub-Γ⊢τ εδ prefix px ∷ sub-cons pxs

  sub-Γ⊢τ-front : Γ ⊢ ε ⦂ σ
                → Γ , σ ⊢ τ
                → Γ ⊢ [ zero ↦τ ε ] τ
  sub-Γ⊢τ-front εδ τδ = sub-Γ⊢τ εδ (prefix-cons prefix-refl) τδ
  {-
  sub-Γ⊢τ εδ (TWF-TrueRef Γok) = TWF-TrueRef (Γok-tail Γok)
  sub-Γ⊢τ εδ (TWF-Base ε₁δ ε₂δ) = {! !}
  sub-Γ⊢τ εδ (TWF-Conj ρ₁δ ρ₂δ) = TWF-Conj (sub-Γ⊢τ εδ ρ₁δ) (sub-Γ⊢τ εδ ρ₂δ)
  sub-Γ⊢τ εδ (TWF-Arr arrδ resδ) = TWF-Arr (sub-Γ⊢τ εδ arrδ) {! !}
  sub-Γ⊢τ {Γ = Γ} {ε = ε} {σ = σ} εδ (TWF-ADT consδs) = TWF-ADT (sub-cons consδs)
    where
      sub-cons : {cons : ADTCons nₐ _}
               → All (λ conτ → (Γ , σ) ⊢ conτ) cons
               → All (λ conτ → Γ ⊢ conτ) ([ zero ↦c ε ] cons)
      sub-cons [] = []
      sub-cons (px ∷ pxs) = sub-Γ⊢τ εδ px ∷ sub-cons pxs
  -}

{-
mutual
  sub-Γok : Γ ⊢ ε ⦂ σ
          → (Γ , x ⦂ σ , Δ) ok
          → (Γ , [ x ↦ₗ ε ] Δ) ok
  sub-Γok {Δ = []} _ (TCTX-Bind prevOk _) = prevOk
  sub-Γok {Δ = (x ,' τ) ∷ Δ} εδ (TCTX-Bind prevOk τδ) = TCTX-Bind (sub-Γok εδ prevOk) (sub-Γ⊢τ εδ τδ)

  sub-Γ⊢τ : Γ ⊢ ε ⦂ σ
          → (Γ , x ⦂ σ , Δ) ⊢ τ'
          → (Γ , [ x ↦ₗ ε ] Δ) ⊢ [ x ↦ₜ ε ] τ'
  sub-Γ⊢τ εδ (TWF-TrueRef gok) = TWF-TrueRef (sub-Γok εδ gok)
  sub-Γ⊢τ εδ (TWF-Base ε₁δ ε₂δ) = TWF-Base (sub-Γ⊢ε⦂τ εδ _ ε₁δ) (sub-Γ⊢ε⦂τ εδ _ ε₂δ)
  sub-Γ⊢τ εδ (TWF-Conj ρ₁δ ρ₂δ) = TWF-Conj (sub-Γ⊢τ εδ ρ₁δ) (sub-Γ⊢τ εδ ρ₂δ)
  sub-Γ⊢τ εδ (TWF-Arr arrδ resδ) = TWF-Arr (sub-Γ⊢τ εδ arrδ) (sub-Γ⊢τ εδ resδ)
  sub-Γ⊢τ {Γ = Γ} {ε = ε} {σ = σ} εδ (TWF-ADT consδs) = TWF-ADT (sub-cons consδs)
    where
      sub-cons : {cons : ADTCons n}
               → All (λ conτ → (Γ , x ⦂ σ , Δ) ⊢ conτ) cons
               → All (λ conτ → (Γ , [ x ↦ₗ ε ] Δ ) ⊢ conτ) ([ x ↦ₐ ε ] cons)
      sub-cons [] = []
      sub-cons (px ∷ pxs) = sub-Γ⊢τ εδ px ∷ sub-cons pxs

  sub-Γ⊢ε⦂τ : Γ ⊢ ε ⦂ σ
            → (ε' : _)
            → (Γ , x ⦂ σ , Δ) ⊢ ε' ⦂ τ'
            → (Γ , [ x ↦ₗ ε ] Δ) ⊢ [ x ↦ₑ ε ] ε' ⦂ [ x ↦ₜ ε ] τ'
  sub-Γ⊢ε⦂τ εδ _  (T-Unit gok) = T-Unit (sub-Γok εδ gok)
  sub-Γ⊢ε⦂τ {x = x} εδ (SVar x') (T-Var gok ∈) with var-eq x x'
  ... | false = T-Var (sub-Γok εδ gok) {! !}
  ... | true = {! !}
  sub-Γ⊢ε⦂τ εδ _  (T-Abs arrδ bodyδ) = {! !}
  sub-Γ⊢ε⦂τ εδ ε' (T-App δ₁ δ₂) = {! !}
  sub-Γ⊢ε⦂τ εδ _  (T-Case resδ δ branches) = {! !}
  sub-Γ⊢ε⦂τ εδ _  (T-Con δ adtτ) = {! !}
  sub-Γ⊢ε⦂τ εδ _  (T-Sub δ x x₁) = {! !}
  -}


Γ⊢ε⦂τ-⇒-Γ⊢τ : Γ ⊢ ε ⦂ τ
            → Γ ⊢ τ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Unit gok) = TWF-TrueRef gok
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Var gok ∈-prf) = τ∈Γ-⇒-Γ⊢τ gok ∈-prf
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Abs arrδ _) = arrδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-App δ₁ δ₂) = sub-Γ⊢τ-front δ₂ (arr-wf-⇒-cod-wf (Γ⊢ε⦂τ-⇒-Γ⊢τ δ₁))
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Case resδ _ _) = resδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Con _ adtτ) = adtτ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Sub δ superδ sub) = superδ
