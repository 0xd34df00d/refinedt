module Surface.Substitutions.Inverse where

open import Agda.Builtin.Equality
open import Data.Bool

open import Surface.Syntax
open import Surface.Substitutions

↦ₑ-inv-SUnit : [ x ↦ₑ ε ] ε' ≡ SUnit → ε' ≡ SUnit
↦ₑ-inv-SUnit {x = x} {ε' = SVar var} ≡prf with var-eq x var
... | eq = {! eq !}
↦ₑ-inv-SUnit {x = x} {ε' = SLam var τ ε'} ≡prf = {! !}
↦ₑ-inv-SUnit {ε' = SUnit} _ = refl

private
  ∈∣-≡-ν : (ν₁ ∈ b₁ ∣ ρ₁) ≡ (ν₂ ∈ b₂ ∣ ρ₂) → ν₁ ≡ ν₂
  ∈∣-≡-ν refl = refl

  ∈∣-≡-b : (ν₁ ∈ b₁ ∣ ρ₁) ≡ (ν₂ ∈ b₂ ∣ ρ₂) → b₁ ≡ b₂
  ∈∣-≡-b refl = refl

  ∈∣-≡-ρ : (ν₁ ∈ b₁ ∣ ρ₁) ≡ (ν₂ ∈ b₂ ∣ ρ₂) → ρ₁ ≡ ρ₂
  ∈∣-≡-ρ refl = refl

  ≈-≡₁ : ε₁ ≈ ε₂ ≡ Τ → ε₁ ≡ SUnit
  ≈-≡₁ refl = refl

  ≈-≡₂ : ε₁ ≈ ε₂ ≡ Τ → ε₂ ≡ SUnit
  ≈-≡₂ refl = refl

  ↦ᵣ-inv-ρ : [ x ↦ᵣ ε ] ρ ≡ Τ → ρ ≡ Τ
  ↦ᵣ-inv-ρ {ρ = x₁ ≈ x₂} ≡prf rewrite ≈-≡₁ ≡prf | ≈-≡₂ ≡prf = {! !}

↦ₜ-inv-ρΤ : [ x ↦ₜ ε ] τ ≡ ν ∈ b ∣ Τ
          → τ ≡ ν ∈ b ∣ Τ
↦ₜ-inv-ρΤ {τ = SRBT ν b ρ} ≡prf rewrite ∈∣-≡-ν ≡prf
                                      | ∈∣-≡-b ≡prf
                                      | ↦ᵣ-inv-ρ (∈∣-≡-ρ ≡prf) = refl
