{-# OPTIONS --safe #-}

module Core.Syntax.Derived where

open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Syntax
open import Core.Syntax.Renaming

infixr 3 _⇒'_
_⇒'_ : CExpr ℓ → CExpr ℓ → CExpr ℓ
τ₁ ⇒' τ₂ = CΠ τ₁ (weaken-ε τ₂)

-- This is the continuation type in the Σ type and constructor:
-- Π x : τ . P x → α
-- It's assumed to be within a context of α, the return type.
Σ-cont : CExpr ℓ → CExpr ℓ → CExpr (suc ℓ)
Σ-cont τ P =
  CΠ
    (weaken-ε τ) {- x -}
    (weaken-ε-k 2 P · CVar zero {- P x -}
        ⇒'
      CVar (suc zero) {- α -}
    )

Σ[_]_ : CExpr ℓ → CExpr ℓ → CExpr ℓ
Σ[ τ ] P =
  CΠ
    ⋆ₑ {- α -}
    (Σ-cont τ P ⇒' CVar zero)

[_⦂_∣_of_] : CExpr ℓ → CExpr ℓ → CExpr ℓ → CExpr ℓ → CExpr ℓ
[ ε ⦂ τ ∣ π of P ] =
  CLam
    ⋆ₑ {- α -}
    (CLam
      (Σ-cont τ P)
      (CVar zero · weaken-ε-k 2 ε · weaken-ε-k 2 π)
    )

×-cont : CExpr ℓ → CExpr ℓ → CExpr (suc ℓ)
×-cont τ₁ τ₂ = weaken-ε τ₁ ⇒' weaken-ε τ₂ ⇒' CVar zero

⟨_×_⟩ : CExpr ℓ → CExpr ℓ → CExpr ℓ
⟨ τ₁ × τ₂ ⟩ = CΠ
                ⋆ₑ
                (×-cont τ₁ τ₂ ⇒' CVar zero)

⟨_⦂_×_⦂_⟩ : (ε₁ τ₁ ε₂ τ₂ : CExpr ℓ) → CExpr ℓ
⟨ ε₁ ⦂ τ₁ × ε₂ ⦂ τ₂ ⟩ = CLam
                          ⋆ₑ
                          (CLam
                            (×-cont τ₁ τ₂)
                            (CVar zero · weaken-ε-k 2 ε₁ · weaken-ε-k 2 ε₂)
                          )

-- TODO ideally we'd like to use the following,
-- but proving its well-typedness requires proving that our operational semantics are normalizing,
-- which is something I don't really want to do yet.
⟨'_×_⟩ : CExpr ℓ → CExpr ℓ → CExpr ℓ
⟨' τ₁ × τ₂ ⟩ = Σ[ τ₁ ] (CLam τ₁ (weaken-ε τ₂))

⟨'_⦂_×_⦂_⟩ : (ε₁ τ₁ ε₂ τ₂ : CExpr ℓ) → CExpr ℓ
⟨' ε₁ ⦂ τ₁ × ε₂ ⦂ τ₂ ⟩ = [ ε₁ ⦂ τ₁ ∣ ε₂ of CLam τ₁ (weaken-ε τ₂) ]

_≡̂_of_ : CExpr ℓ → CExpr ℓ → CExpr ℓ → CExpr ℓ
ε₁ ≡̂ ε₂ of τ = CΠ (τ ⇒' ⋆ₑ) ⟨ CVar zero · weaken-ε ε₁ ⇒' CVar zero · weaken-ε ε₂
                            × CVar zero · weaken-ε ε₂ ⇒' CVar zero · weaken-ε ε₁
                            ⟩

eq-refl : CExpr ℓ → CExpr ℓ → CExpr ℓ
eq-refl τ ε =
  CLam (τ ⇒' ⋆ₑ) ⟨ id-fun ⦂ id-fun-type × id-fun ⦂ id-fun-type ⟩
  where
  Pε          = CVar zero · weaken-ε ε
  id-fun      = CLam Pε (CVar zero)
  id-fun-type = Pε ⇒' Pε


-- Helpers for the above
≡̂-subst : (ε₁ ≡ ε₁')
        → (ε₂ ≡ ε₂')
        → (τ  ≡ τ')
        → ε₁ ≡̂ ε₂ of τ ≡ ε₁' ≡̂ ε₂' of τ'
≡̂-subst refl refl refl = refl
