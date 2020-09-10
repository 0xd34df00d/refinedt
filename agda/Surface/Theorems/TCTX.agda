module Surface.Theorems.TCTX where

open import Surface.Syntax
open import Surface.Derivations
open import Surface.Theorems.Helpers

abstract
  Γ⊢ε⦂τ-implies-Γok : Γ ⊢ ε ⦂ τ → Γ ok
  Γ⊢ε⦂τ-implies-Γok (T-Unit gok) = gok
  Γ⊢ε⦂τ-implies-Γok (T-Var gok _) = gok
  Γ⊢ε⦂τ-implies-Γok (T-Abs _ bodyδ) = Γok-tail (Γ⊢ε⦂τ-implies-Γok bodyδ)
  Γ⊢ε⦂τ-implies-Γok (T-App _ δ₂) = Γ⊢ε⦂τ-implies-Γok δ₂
  Γ⊢ε⦂τ-implies-Γok (T-Case _ scrut _) = Γ⊢ε⦂τ-implies-Γok scrut
  Γ⊢ε⦂τ-implies-Γok (T-Con conArg _) = Γ⊢ε⦂τ-implies-Γok conArg
  Γ⊢ε⦂τ-implies-Γok (T-Sub δ _) = Γ⊢ε⦂τ-implies-Γok δ

  Γ⊢τ-implies-Γok : Γ ⊢ τ → Γ ok
  Γ⊢τ-implies-Γok (TWF-TrueRef gok) = gok
  Γ⊢τ-implies-Γok (TWF-Base ε₁δ _) = Γok-tail (Γ⊢ε⦂τ-implies-Γok ε₁δ)
  Γ⊢τ-implies-Γok (TWF-Conj ρ₁δ _) = Γ⊢τ-implies-Γok ρ₁δ
  Γ⊢τ-implies-Γok (TWF-Arr argδ _) = Γ⊢τ-implies-Γok argδ
  Γ⊢τ-implies-Γok (TWF-ADT (px ∷ _)) = Γ⊢τ-implies-Γok px
