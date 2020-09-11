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

  Γ⊢ε⦂τ-⇒-Γok-smaller : (δ : Γ ⊢ ε ⦂ τ)
                      → size-ok (Γ⊢ε⦂τ-⇒-Γok δ) < size-t δ
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Unit gok) = s≤s (≤-reflexive refl)
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Var gok x) = s≤s (≤-reflexive refl)
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Abs arrδ bodyδ) = let <1 = Γok-tail-smaller (Γ⊢ε⦂τ-⇒-Γok bodyδ)
                                               <2 = Γ⊢ε⦂τ-⇒-Γok-smaller bodyδ
                                               <3 = <-trans <1 <2
                                            in <-trans <3 (s≤s (n≤m<>n (size-twf arrδ) (size-t bodyδ)))
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-App δ₁ δ₂) = <-trans (Γ⊢ε⦂τ-⇒-Γok-smaller δ₂) (s≤s (n≤m<>n (size-t δ₁) (size-t δ₂)))
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Case resδ scrutδ branches) = let rec = Γ⊢ε⦂τ-⇒-Γok-smaller scrutδ
                                                       in <-trans rec (s≤s (m≤m<>n (size-t scrutδ) (size-twf resδ ⊔ _)))
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Con x adtτ) = <-trans (Γ⊢ε⦂τ-⇒-Γok-smaller x) (s≤s (m≤m<>n (size-t x) (size-twf adtτ)))
  Γ⊢ε⦂τ-⇒-Γok-smaller (T-Sub δ sub) = <-trans (Γ⊢ε⦂τ-⇒-Γok-smaller δ) (s≤s (m≤m<>n (size-t δ) (size-st sub)))
