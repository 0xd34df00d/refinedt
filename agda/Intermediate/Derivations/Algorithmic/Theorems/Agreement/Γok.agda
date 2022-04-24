{-# OPTIONS --safe #-}

module Intermediate.Derivations.Algorithmic.Theorems.Agreement.Γok where

open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Nat.Base
open import Data.Nat.Properties

open import Intermediate.Syntax
open import Intermediate.Derivations.Algorithmic
open import Intermediate.Derivations.Algorithmic.Theorems.Helpers
open import Intermediate.Derivations.Algorithmic.Theorems.Agreement.Γok.WF

Γok-tail-smaller : (δ : [ θ ] (Γ , τ) ok)
                 → size-ok (Γok-tail δ) < size-ok δ
Γok-tail-smaller (TCTX-Bind prevOk τδ) = s≤s (₁≤₂ (size-ok prevOk) (size-twf τδ))

-- Referred to as T-implies-TCTX in the paper
mutual
  Γ⊢ε⦂τ-⇒-Γok : [ θ ] Γ ⊢ ε ⦂ τ → [ θ ] Γ ok
  Γ⊢ε⦂τ-⇒-Γok (T-Unit gok) = gok
  Γ⊢ε⦂τ-⇒-Γok (T-Var gok _) = gok
  Γ⊢ε⦂τ-⇒-Γok (T-Abs arrδ _) = Γ⊢τ-⇒-Γok arrδ
  Γ⊢ε⦂τ-⇒-Γok (T-App δ₁ _ _ _) = Γ⊢ε⦂τ-⇒-Γok δ₁
  Γ⊢ε⦂τ-⇒-Γok (T-Case _ scrut _) = Γ⊢ε⦂τ-⇒-Γok scrut
  Γ⊢ε⦂τ-⇒-Γok (T-Con _ conArg _) = Γ⊢ε⦂τ-⇒-Γok conArg
  Γ⊢ε⦂τ-⇒-Γok (T-SubW _ εδ) = Γ⊢ε⦂τ-⇒-Γok εδ

  -- Referred to as TWF-implies-TCTX in the paper
  Γ⊢τ-⇒-Γok : [ θ ] Γ ⊢ τ → [ θ ] Γ ok
  Γ⊢τ-⇒-Γok (TWF-TrueRef gok) = gok
  Γ⊢τ-⇒-Γok (TWF-Base ε₁δ _) = Γok-tail (Γ⊢ε⦂τ-⇒-Γok ε₁δ)
  Γ⊢τ-⇒-Γok (TWF-Conj ρ₁δ _) = Γ⊢τ-⇒-Γok ρ₁δ
  Γ⊢τ-⇒-Γok (TWF-Arr argδ _) = Γ⊢τ-⇒-Γok argδ
  Γ⊢τ-⇒-Γok (TWF-ADT (px ∷ _)) = Γ⊢τ-⇒-Γok px

private
  a<b-⇒-a<b⊕c : {b c a : ℕ} → a < b → a < suc (b ⊕ c)
  a<b-⇒-a<b⊕c {b} {c} a<b = <-trans a<b (s≤s (₁≤₂ b c))

  a<c-⇒-a<b⊕c : {b c a : ℕ} → a < c → a < suc (b ⊕ c)
  a<c-⇒-a<b⊕c {b} {c} a<c = <-trans a<c (s≤s (₂≤₂ b c))

abstract
  mutual
    Γ⊢ε⦂τ-⇒-Γok-smaller : (δ : [ θ ] Γ ⊢ ε ⦂ τ)
                        → size-ok (Γ⊢ε⦂τ-⇒-Γok δ) < size-t δ
    Γ⊢ε⦂τ-⇒-Γok-smaller (T-Unit _) = s≤s (≤-step ≤-refl)
    Γ⊢ε⦂τ-⇒-Γok-smaller (T-Var _ _) = s≤s ≤-refl
    Γ⊢ε⦂τ-⇒-Γok-smaller (T-Abs arrδ _) = a<b-⇒-a<b⊕c (Γ⊢τ-⇒-Γok-smaller arrδ)
    Γ⊢ε⦂τ-⇒-Γok-smaller (T-App δ₁ _ _ _) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-smaller δ₁)
    Γ⊢ε⦂τ-⇒-Γok-smaller (T-Case _ scrutδ _) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-smaller scrutδ)
    Γ⊢ε⦂τ-⇒-Γok-smaller (T-Con _ conArg (TWF-ADT _)) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-smaller conArg)
    Γ⊢ε⦂τ-⇒-Γok-smaller (T-SubW _ εδ) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-smaller εδ)

    Γ⊢ε⦂τ-⇒-Γok-tail-smaller : (δ : [ θ ] (Γ , τ') ⊢ ε ⦂ τ)
                             → size-ok (Γok-tail (Γ⊢ε⦂τ-⇒-Γok δ)) < size-t δ
    Γ⊢ε⦂τ-⇒-Γok-tail-smaller δ = <-trans (Γok-tail-smaller (Γ⊢ε⦂τ-⇒-Γok δ)) (Γ⊢ε⦂τ-⇒-Γok-smaller δ)

    Γ⊢τ-⇒-Γok-smaller : (δ : [ θ ] Γ ⊢ τ)
                      → size-ok (Γ⊢τ-⇒-Γok δ) < size-twf δ
    Γ⊢τ-⇒-Γok-smaller (TWF-TrueRef _) = s≤s ≤-refl
    Γ⊢τ-⇒-Γok-smaller (TWF-Base ε₁δ _) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-tail-smaller ε₁δ)
    Γ⊢τ-⇒-Γok-smaller (TWF-Conj ρ₁δ _) = a<b-⇒-a<b⊕c (Γ⊢τ-⇒-Γok-smaller ρ₁δ)
    Γ⊢τ-⇒-Γok-smaller (TWF-Arr argδ _) = a<b-⇒-a<b⊕c (Γ⊢τ-⇒-Γok-smaller argδ)
    Γ⊢τ-⇒-Γok-smaller (TWF-ADT (px ∷ pxs)) = <-trans
                                               (a<b-⇒-a<b⊕c (Γ⊢τ-⇒-Γok-smaller px))
                                               (n<1+n (suc (size-twf px ⊔ size-all-cons pxs)))
