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

-- Substitution lemmas

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
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-App δ₁ δ₂) = sub-Γ⊢τ δ₂ (arr-wf-⇒-cod-wf (Γ⊢ε⦂τ-⇒-Γ⊢τ δ₁))
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Case resδ _ _) = resδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Con _ adtτ) = adtτ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Sub δ superδ sub) = superδ
