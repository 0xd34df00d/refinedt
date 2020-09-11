module Surface.Theorems.TCTX where

open import Agda.Builtin.Equality
open import Data.Nat.Properties

open import Surface.Syntax
open import Surface.Derivations
open import Surface.Derivations.WF
open import Surface.Theorems.Helpers

abstract
  Γ⊢ε⦂τ-⇒-Γok : Γ ⊢ ε ⦂ τ → Γ ok
  Γ⊢ε⦂τ-⇒-Γok (T-Unit gok) = gok
  Γ⊢ε⦂τ-⇒-Γok (T-Var gok _) = gok
  Γ⊢ε⦂τ-⇒-Γok (T-Abs _ bodyδ) = Γok-tail (Γ⊢ε⦂τ-⇒-Γok bodyδ)
  Γ⊢ε⦂τ-⇒-Γok (T-App _ δ₂) = Γ⊢ε⦂τ-⇒-Γok δ₂
  Γ⊢ε⦂τ-⇒-Γok (T-Case _ scrut _) = Γ⊢ε⦂τ-⇒-Γok scrut
  Γ⊢ε⦂τ-⇒-Γok (T-Con conArg _) = Γ⊢ε⦂τ-⇒-Γok conArg
  Γ⊢ε⦂τ-⇒-Γok (T-Sub δ _) = Γ⊢ε⦂τ-⇒-Γok δ

  Γ⊢τ-⇒-Γok : Γ ⊢ τ → Γ ok
  Γ⊢τ-⇒-Γok (TWF-TrueRef gok) = gok
  Γ⊢τ-⇒-Γok (TWF-Base ε₁δ _) = Γok-tail (Γ⊢ε⦂τ-⇒-Γok ε₁δ)
  Γ⊢τ-⇒-Γok (TWF-Conj ρ₁δ _) = Γ⊢τ-⇒-Γok ρ₁δ
  Γ⊢τ-⇒-Γok (TWF-Arr argδ _) = Γ⊢τ-⇒-Γok argδ
  Γ⊢τ-⇒-Γok (TWF-ADT (px ∷ _)) = Γ⊢τ-⇒-Γok px

  Γ⊢ε⦂τ-⇒-Γok-tail-smaller : (δ : (Γ , x ⦂ τ') ⊢ ε ⦂ τ)
                           → size-ok (Γok-tail (Γ⊢ε⦂τ-⇒-Γok δ)) < size-t δ

  private
    a<b-⇒-a<b<>c : {b c a : ℕ} → a < b → a < suc (b <> c)
    a<b-⇒-a<b<>c {b} {c} a<b = <-trans a<b (s≤s (m≤m<>n b c))

    a<c-⇒-a<b<>c : {b c a : ℕ} → a < c → a < suc (b <> c)
    a<c-⇒-a<b<>c {b} {c} a<c = <-trans a<c (s≤s (n≤m<>n b c))

  Γ⊢ε⦂τ-⇒-Γok-smaller : (δ : Γ ⊢ ε ⦂ τ)
                      → size-ok (Γ⊢ε⦂τ-⇒-Γok δ) < size-t δ
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Unit gok) = s≤s (≤-reflexive refl)
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Var gok x) = s≤s (≤-reflexive refl)
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Abs arrδ bodyδ) = a<c-⇒-a<b<>c (Γ⊢ε⦂τ-⇒-Γok-tail-smaller bodyδ)
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-App δ₁ δ₂) = a<c-⇒-a<b<>c (Γ⊢ε⦂τ-⇒-Γok-smaller δ₂)
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Case resδ scrutδ branches) = a<b-⇒-a<b<>c (Γ⊢ε⦂τ-⇒-Γok-smaller scrutδ)
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Con conArg adtτ) = a<b-⇒-a<b<>c (Γ⊢ε⦂τ-⇒-Γok-smaller conArg)
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Sub δ sub) = a<b-⇒-a<b<>c (Γ⊢ε⦂τ-⇒-Γok-smaller δ)

  Γ⊢ε⦂τ-⇒-Γok-tail-smaller δ = <-trans (Γok-tail-smaller (Γ⊢ε⦂τ-⇒-Γok δ)) (Γ⊢ε⦂τ-⇒-Γok-smaller δ)

  Γ⊢τ-⇒-Γok-smaller : (δ : Γ ⊢ τ)
                    → size-ok (Γ⊢τ-⇒-Γok δ) < size-twf δ
  Γ⊢τ-⇒-Γok-smaller (TWF-TrueRef gok) = s≤s (≤-reflexive refl)
  Γ⊢τ-⇒-Γok-smaller (TWF-Base ε₁δ ε₂δ) = a<b-⇒-a<b<>c (Γ⊢ε⦂τ-⇒-Γok-tail-smaller ε₁δ)
  Γ⊢τ-⇒-Γok-smaller (TWF-Conj ρ₁δ ρ₂δ) = a<b-⇒-a<b<>c (Γ⊢τ-⇒-Γok-smaller ρ₁δ)
  Γ⊢τ-⇒-Γok-smaller (TWF-Arr argδ resδ) = a<b-⇒-a<b<>c (Γ⊢τ-⇒-Γok-smaller argδ)
  Γ⊢τ-⇒-Γok-smaller (TWF-ADT (px ∷ consδs)) = a<b-⇒-a<b<>c (Γ⊢τ-⇒-Γok-smaller px)
