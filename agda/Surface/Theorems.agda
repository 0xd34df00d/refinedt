{-# OPTIONS --safe #-}

module Surface.Theorems where

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
open import Surface.Derivations
open import Surface.Derivations.WF
open import Surface.Theorems.TCTX
open import Surface.Theorems.Helpers
open import Surface.Theorems.Thinning
open import Surface.Theorems.SubstTyping

-- Substitution lemmas

-- Some local helpers

τ∈Γ-⇒-Γ⊢τ : Γ ok → τ ∈ Γ at ι → Γ ⊢ τ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind δ τδ) (∈-zero refl) = twf-weakening δ τδ τδ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind δ τδ) (∈-suc refl ∈) = twf-weakening δ τδ (τ∈Γ-⇒-Γ⊢τ δ ∈)

-- Referred to as T-implies-TWF in the paper
Γ⊢ε⦂τ-⇒-Γ⊢τ : Γ ⊢ ε ⦂ τ
            → Γ ⊢ τ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Unit gok) = TWF-TrueRef gok
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Var gok ∈-prf) = τ∈Γ-⇒-Γ⊢τ gok ∈-prf
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Abs arrδ _) = arrδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-App δ₁ δ₂) = sub-Γ⊢τ-front δ₂ (arr-wf-⇒-cod-wf (Γ⊢ε⦂τ-⇒-Γ⊢τ δ₁))
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Case resδ _ _) = resδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Con _ _ adtτ) = adtτ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Sub δ superδ sub) = superδ
