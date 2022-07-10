{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Thinning.Size.Helpers where

open import Data.Nat
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Data.Nat.Tactic.RingSolver
open import Function
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂)
open Eq.≡-Reasoning

lemma₁ : {[τ₁δ'] [τ₁δ] [εδ'] [εδ] [Γok'] [Γok] : ℕ}
       → [τ₁δ'] + [Γok] ≡ [τ₁δ] + [Γok']
       → [εδ'] + suc [τ₁δ] ≡ [εδ] + suc [τ₁δ']
       → [εδ'] + [Γok] ≡ [εδ] + [Γok']
lemma₁ {[τ₁δ']} {[τ₁δ]} {[εδ']} {[εδ]} {[Γok']} {[Γok]} ≡₁ ≡₂
  = +-cancelʳ-≡ _ _ $
          begin
            ([εδ'] + [Γok]) + (suc [τ₁δ] + [τ₁δ'])
          ≡⟨ lhs-prf [εδ'] _ _ _ ⟩
            ([εδ'] + suc [τ₁δ]) + ([τ₁δ'] + [Γok])
          ≡⟨ cong₂ _+_ ≡₂ ≡₁ ⟩
            ([εδ] + suc [τ₁δ']) + ([τ₁δ] + [Γok'])
          ≡⟨ rhs-prf [εδ]  _ _ _ ⟩
            ([εδ] + [Γok']) + (suc [τ₁δ] + [τ₁δ'])
          ∎
  where
  lhs-prf : (a' b c' d : ℕ)
          → (a' + d) + (b + c') ≡ (a' + b) + (c' + d)
  lhs-prf = solve-∀

  rhs-prf : (a b' c d' : ℕ)
          → (a + suc b') + (c + d') ≡ (a + d') + (suc c + b')
  rhs-prf = solve-∀
