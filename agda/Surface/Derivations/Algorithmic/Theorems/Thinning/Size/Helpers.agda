{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Thinning.Size.Helpers where

open import Data.Nat
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Data.Nat.Tactic.RingSolver
open import Data.List
open import Function
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂; sym)
open Eq.≡-Reasoning

open import Surface.Syntax
open import Surface.Derivations.Algorithmic hiding (_∷_)
open import Surface.Derivations.Algorithmic.Theorems.Agreement.Γok.WF
open import Surface.Derivations.Algorithmic.Theorems.Uniqueness

lemma₀ : (τ₁δ : Γ ⊢[ θ , φ ] τ₁)
       → (τ₂δ : Γ , τ₁ ⊢[ θ , φ ] τ₂)
       → (τ₁⇒τ₂δ : Γ ⊢[ θ , φ ] τ₁ ⇒ τ₂)
       → suc (size-twf τ₁δ ⊔ size-twf τ₂δ) ≡ size-twf τ₁⇒τ₂δ
lemma₀ τ₁δ τ₂δ (TWF-Arr τ₁δ' τ₂δ')
  rewrite unique-Γ⊢τ τ₁δ' τ₁δ
        | unique-Γ⊢τ τ₂δ' τ₂δ
        = refl

lemma₁ : {[τ₁δ'] [τ₁δ] [εδ'] [εδ] [Γok'] [Γok] : ℕ}
       → [τ₁δ'] + [Γok] ≡ [τ₁δ] + [Γok']
       → [εδ'] + suc [τ₁δ] ≡ [εδ] + suc [τ₁δ']
       → [εδ'] + [Γok] ≡ [εδ] + [Γok']
lemma₁ {[τ₁δ']} {[τ₁δ]} {[εδ']} {[εδ]} {[Γok']} {[Γok]} ≡₁ ≡₂ = +-cancelʳ-≡ _ _ $
  begin
    ([εδ'] + [Γok]) + (suc [τ₁δ] + [τ₁δ'])
  ≡⟨ solve ([εδ'] ∷ [Γok] ∷ [τ₁δ] ∷ [τ₁δ'] ∷ []) ⟩
    ([εδ'] + suc [τ₁δ]) + ([τ₁δ'] + [Γok])
  ≡⟨ cong₂ _+_ ≡₂ ≡₁ ⟩
    ([εδ] + suc [τ₁δ']) + ([τ₁δ] + [Γok'])
  ≡⟨ solve ([εδ] ∷ [Γok'] ∷ [τ₁δ'] ∷ [τ₁δ] ∷ []) ⟩
    ([εδ] + [Γok']) + (suc [τ₁δ] + [τ₁δ'])
  ∎

+-distribʳ-⊔³ : (a b c z : ℕ)
              → a ⊔ (b ⊔ c) + z ≡ (a + z) ⊔ (b + z) ⊔ (c + z)
+-distribʳ-⊔³ a b c z
  rewrite +-distribʳ-⊔ z a (b ⊔ c)
        | +-distribʳ-⊔ z b c
        = sym (⊔-assoc (a + z) (b + z) (c + z))

cong₃ : {A B C D : Set}
      → ∀ {a₁ a₂ b₁ b₂ c₁ c₂}
      → (f : A → B → C → D)
      → a₁ ≡ a₂
      → b₁ ≡ b₂
      → c₁ ≡ c₂
      → f a₁ b₁ c₁ ≡ f a₂ b₂ c₂
cong₃ _ refl refl refl = refl
