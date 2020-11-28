{-# OPTIONS --safe #-}

module Surface.Theorems where

open import Agda.Builtin.Equality
open import Data.Bool.Base
open import Data.Fin.Base using (fromℕ<)
open import Data.Nat.Properties using (≤-stepsʳ; ≤-refl)
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
[_↦Γ_]_ : ∀ {k} ℓ
        → (ε : STerm ℓ)
        → Ctx (suc (k + ℓ))
        → Ctx (k + ℓ)
[_↦Γ_]_ {k = zero} ℓ ε (Γ , _) = Γ
[_↦Γ_]_ {k = suc k} ℓ ε (Γ,Δ , τ) = ([ ℓ ↦Γ ε ] Γ,Δ) , ([ ctx-idx ℓ ↦τ R.weaken-ε-k k ε ] τ)

-- Substitution lemmas

mutual
  sub-Γok : ∀ k {Γ : Ctx (suc (k + ℓ))} {τ : SType (suc (k + ℓ))}
          → Γ ⊢ R.weaken-ε-k (suc k) ε ⦂ R.weaken-τ-k (suc k) σ
          → Γ ok
          → ([ ℓ ↦Γ ε ] Γ) ok
  sub-Γok zero {Γ , _} εδ (TCTX-Bind Γok τδ) = Γok
  sub-Γok (suc k) {Γ , x} εδ (TCTX-Bind Γok τδ) = TCTX-Bind {! sub-Γok !} {! !}

  sub-Γ⊢τ : ∀ k {Γ : Ctx (suc (k + ℓ))} {τ : SType (suc (k + ℓ))}
          → Γ ⊢ R.weaken-ε-k (suc k) ε ⦂ R.weaken-τ-k (suc k) σ
          → Γ ⊢ τ
          → [ ℓ ↦Γ ε ] Γ ⊢ [ ctx-idx ℓ ↦τ R.weaken-ε-k k ε ] τ
  sub-Γ⊢τ k εδ (TWF-TrueRef Γok) = TWF-TrueRef (sub-Γok k εδ Γok)
  sub-Γ⊢τ k εδ (TWF-Base ε₁δ ε₂δ) = {! !}
  sub-Γ⊢τ k εδ (TWF-Conj ρ₁δ ρ₂δ) = TWF-Conj (sub-Γ⊢τ k εδ ρ₁δ) (sub-Γ⊢τ k εδ ρ₂δ)
  sub-Γ⊢τ k εδ (TWF-Arr arrδ resδ) = TWF-Arr (sub-Γ⊢τ k εδ arrδ) {! !}
  sub-Γ⊢τ k εδ (TWF-ADT consδs) = {! !}

  sub-Γ⊢τ-front : Γ ⊢ ε ⦂ σ
                → Γ , σ ⊢ τ
                → Γ ⊢ [ zero ↦τ ε ] τ
  sub-Γ⊢τ-front εδ τδ = sub-Γ⊢τ zero (t-weakening (Γ⊢ε⦂τ-⇒-Γok εδ) (Γok-head (Γ⊢τ-⇒-Γok τδ)) εδ) τδ
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
