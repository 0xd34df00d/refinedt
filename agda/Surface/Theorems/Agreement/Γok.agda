{-# OPTIONS --safe #-}

module Surface.Theorems.Agreement.Γok where

open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Nat.Base
open import Data.Nat.Properties

open import Surface.Syntax
open import Surface.Derivations
open import Surface.Theorems.Helpers
open import Surface.Theorems.Agreement.Γok.WF

Γok-tail-smaller : (δ : (Γ , τ) ok) → size-ok (Γok-tail δ) < size-ok δ
Γok-tail-smaller (TCTX-Bind prevOk τδ) = s≤s (m≤m⊕n (size-ok prevOk) (size-twf τδ))

abstract
  -- Referred to as T-implies-TCTX in the paper
  Γ⊢ε⦂τ-⇒-Γok : Γ ⊢ ε ⦂ τ → Γ ok
  Γ⊢ε⦂τ-⇒-Γok (T-Unit gok) = gok
  Γ⊢ε⦂τ-⇒-Γok (T-Var gok _) = gok
  Γ⊢ε⦂τ-⇒-Γok (T-Abs _ bodyδ) = Γok-tail (Γ⊢ε⦂τ-⇒-Γok bodyδ)
  Γ⊢ε⦂τ-⇒-Γok (T-App _ δ₂) = Γ⊢ε⦂τ-⇒-Γok δ₂
  Γ⊢ε⦂τ-⇒-Γok (T-Case _ scrut _) = Γ⊢ε⦂τ-⇒-Γok scrut
  Γ⊢ε⦂τ-⇒-Γok (T-Con _ conArg _) = Γ⊢ε⦂τ-⇒-Γok conArg
  Γ⊢ε⦂τ-⇒-Γok (T-Sub δ _ _) = Γ⊢ε⦂τ-⇒-Γok δ
  Γ⊢ε⦂τ-⇒-Γok (T-RConv δ _ _) = Γ⊢ε⦂τ-⇒-Γok δ

  -- Referred to as TWF-implies-TCTX in the paper
  Γ⊢τ-⇒-Γok : Γ ⊢ τ → Γ ok
  Γ⊢τ-⇒-Γok (TWF-TrueRef gok) = gok
  Γ⊢τ-⇒-Γok (TWF-Base ε₁δ _) = Γok-tail (Γ⊢ε⦂τ-⇒-Γok ε₁δ)
  Γ⊢τ-⇒-Γok (TWF-Conj ρ₁δ _) = Γ⊢τ-⇒-Γok ρ₁δ
  Γ⊢τ-⇒-Γok (TWF-Arr argδ _) = Γ⊢τ-⇒-Γok argδ
  Γ⊢τ-⇒-Γok (TWF-ADT (px ∷ _)) = Γ⊢τ-⇒-Γok px

  Γ⊢ε⦂τ-⇒-Γok-tail-smaller : (δ : (Γ , τ') ⊢ ε ⦂ τ)
                           → size-ok (Γok-tail (Γ⊢ε⦂τ-⇒-Γok δ)) < size-t δ

  private
    a<b-⇒-a<b⊕c : {b c a : ℕ} → a < b → a < suc (b ⊕ c)
    a<b-⇒-a<b⊕c {b} {c} a<b = <-trans a<b (s≤s (m≤m⊕n b c))

    a<c-⇒-a<b⊕c : {b c a : ℕ} → a < c → a < suc (b ⊕ c)
    a<c-⇒-a<b⊕c {b} {c} a<c = <-trans a<c (s≤s (n≤m⊕n b c))

  Γ⊢ε⦂τ-⇒-Γok-smaller : (δ : Γ ⊢ ε ⦂ τ)
                      → size-ok (Γ⊢ε⦂τ-⇒-Γok δ) < size-t δ
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Unit _) = s≤s (≤-step ≤-refl)
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Var _ _) = s≤s ≤-refl
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Abs _ bodyδ) = a<c-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-tail-smaller bodyδ)
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-App _ δ₂) = a<c-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-smaller δ₂)
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Case _ scrutδ _) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-smaller scrutδ)
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Con _ conArg _) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-smaller conArg)
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Sub δ _ _) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-smaller δ)
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-RConv δ _ _) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-smaller δ)

  Γ⊢ε⦂τ-⇒-Γok-tail-smaller δ = <-trans (Γok-tail-smaller (Γ⊢ε⦂τ-⇒-Γok δ)) (Γ⊢ε⦂τ-⇒-Γok-smaller δ)

  Γ⊢τ-⇒-Γok-smaller : (δ : Γ ⊢ τ)
                    → size-ok (Γ⊢τ-⇒-Γok δ) < size-twf δ
  Γ⊢τ-⇒-Γok-smaller (TWF-TrueRef _) = s≤s ≤-refl
  Γ⊢τ-⇒-Γok-smaller (TWF-Base ε₁δ _) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-tail-smaller ε₁δ)
  Γ⊢τ-⇒-Γok-smaller (TWF-Conj ρ₁δ _) = a<b-⇒-a<b⊕c (Γ⊢τ-⇒-Γok-smaller ρ₁δ)
  Γ⊢τ-⇒-Γok-smaller (TWF-Arr argδ _) = a<b-⇒-a<b⊕c (Γ⊢τ-⇒-Γok-smaller argδ)
  Γ⊢τ-⇒-Γok-smaller (TWF-ADT (px ∷ pxs)) = <-trans
                                             (a<b-⇒-a<b⊕c (Γ⊢τ-⇒-Γok-smaller px))
                                             (n<1+n (suc (size-twf px ⊔ size-all-cons pxs)))
