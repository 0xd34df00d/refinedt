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

open import Surface.Syntax hiding (b; b')
open import Surface.Derivations.Algorithmic hiding (_∷_)
open import Surface.Derivations.Algorithmic.Theorems.Agreement.Γok.WF
open import Surface.Derivations.Algorithmic.Theorems.Uniqueness

private variable
  a a' b b' c c' : ℕ

un-suc : a + (suc b) ≡ a' + (suc b')
       → a + b ≡ a' + b'
un-suc {a} {b} {a'} {b'} eq = suc-injective $ begin
  1 + (a + b)     ≡⟨ solve (a ∷ b ∷ []) ⟩
  a + (1 + b)     ≡⟨ eq ⟩
  a' + (1 + b')   ≡⟨ solve (a' ∷ b' ∷ []) ⟩
  1 + (a' + b')   ∎

lemma₀ : (τ₁δ : Γ ⊢[ θ , φ ] τ₁)
       → (τ₂δ : Γ , τ₁ ⊢[ θ , φ ] τ₂)
       → (τ₁⇒τ₂δ : Γ ⊢[ θ , φ ] τ₁ ⇒ τ₂)
       → suc (size-twf τ₁δ ⊔ size-twf τ₂δ) ≡ size-twf τ₁⇒τ₂δ
lemma₀ τ₁δ τ₂δ (TWF-Arr τ₁δ' τ₂δ')
  rewrite unique-Γ⊢τ τ₁δ' τ₁δ
        | unique-Γ⊢τ τ₂δ' τ₂δ
        = refl

lemma₁ : a' + c ≡ a + c'
       → b' + a ≡ b + a'
       → b' + c ≡ b + c'
lemma₁ {a'} {c} {a} {c'} {b'} {b} ≡₁ ≡₂ = +-cancelʳ-≡ _ _ $ begin
  (b' + c) + (a + a')   ≡⟨ solve (b' ∷ c ∷ a ∷ a' ∷ []) ⟩
  (b' + a) + (a' + c)   ≡⟨ cong₂ _+_ ≡₂ ≡₁ ⟩
  (b + a') + (a + c')   ≡⟨ solve (b ∷ c' ∷ a' ∷ a ∷ []) ⟩
  (b + c') + (a + a')   ∎

lemma₂ : a' + c ≡ a + c'
       → b' + suc a ≡ b + suc a'
       → b' + c ≡ b + c'
lemma₂ {a'} {c} {a} {c'} {b'} {b} ≡₁ ≡₂ = lemma₁ {a'} {c} {a} {c'} {b'} {b} ≡₁ (un-suc ≡₂)

+-distribʳ-⊔³ : (a b c z : ℕ)
              → a ⊔ (b ⊔ c) + z ≡ (a + z) ⊔ (b + z) ⊔ (c + z)
+-distribʳ-⊔³ a b c z
  rewrite +-distribʳ-⊔ z a (b ⊔ c)
        | +-distribʳ-⊔ z b c
        = sym (⊔-assoc (a + z) (b + z) (c + z))

+-distribʳ-⊔⁴ : (a b c d z : ℕ)
              → a ⊔ (b ⊔ (c ⊔ d)) + z ≡ (a + z) ⊔ (b + z) ⊔ (c + z) ⊔ (d + z)
+-distribʳ-⊔⁴ a b c d z
  rewrite +-distribʳ-⊔ z a (b ⊔ (c ⊔ d))
        | +-distribʳ-⊔ z b (c ⊔ d)
        | +-distribʳ-⊔ z c d
        = let a' = a + z
              b' = b + z
              c' = c + z
              d' = d + z
           in begin
          a' ⊔ (b' ⊔ (c' ⊔ d')) ≡⟨ sym (⊔-assoc a' b' (c' ⊔ d')) ⟩
          (a' ⊔ b') ⊔ (c' ⊔ d') ≡⟨ sym (⊔-assoc (a' ⊔ b') c' d')  ⟩
          ((a' ⊔ b') ⊔ c') ⊔ d' ∎

cong₃ : {A B C D : Set}
      → ∀ {a₁ a₂ b₁ b₂ c₁ c₂}
      → (f : A → B → C → D)
      → a₁ ≡ a₂
      → b₁ ≡ b₂
      → c₁ ≡ c₂
      → f a₁ b₁ c₁ ≡ f a₂ b₂ c₂
cong₃ _ refl refl refl = refl

⊔-+-pairwise-≡ : (c c' : ℕ)
               → a' + c ≡ a + c'
               → b' + c ≡ b + c'
               → a' ⊔ b' + c ≡ a ⊔ b + c'
⊔-+-pairwise-≡ {a'} {a} {b'} {b} c c' ≡₁ ≡₂ = begin
  a' ⊔ b' + c           ≡⟨ +-distribʳ-⊔ c a' _ ⟩
  (a' + c) ⊔ (b' + c)   ≡⟨ cong₂ (_⊔_) ≡₁ ≡₂ ⟩
  (a + c') ⊔ (b + c')   ≡⟨ sym (+-distribʳ-⊔ c' a _) ⟩
  a ⊔ b + c'            ∎
