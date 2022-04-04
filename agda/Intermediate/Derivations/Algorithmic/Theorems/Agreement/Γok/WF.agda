{-# OPTIONS --safe #-}

{-
This module defines a notion of the size of a derivation that is
strong enough to prove agreement lemmas yielding a witness of `Γ ok`,
but not strong enough to prove the lemma `Γ ⊢ ε ⦂ τ → Γ ⊢ τ`.
-}

module Intermediate.Derivations.Algorithmic.Theorems.Agreement.Γok.WF where

open import Data.Nat.Base using (_⊔_; _≤_)
open import Data.Nat.Properties

open import Intermediate.Syntax
open import Intermediate.Derivations.Algorithmic

size-ok  : [ θ ] Γ ok         → ℕ
size-twf : [ θ ] Γ ⊢ τ        → ℕ
size-t   : [ θ ] Γ ⊢ ε ⦂ τ    → ℕ
size-<:  : [ θ ] Γ ⊢ τ₁ <: τ₂ → ℕ
size-bs  : ∀ {τ cons} {bs : CaseBranches nₐ ℓ}
         → BranchesHaveType θ Γ cons bs τ
         → ℕ
size-all-cons : {cons : ADTCons nₐ ℓ} → All ([ θ ] Γ ⊢_) cons → ℕ

infixr 20 _⊕_
_⊕_ : ℕ → ℕ → ℕ
_⊕_ = _⊔_

abstract
  ₁≤₂ : ∀ m n → m ≤ m ⊕ n
  ₁≤₂ = m≤m⊔n

  ₂≤₂ : ∀ m n → n ≤ m ⊕ n
  ₂≤₂ = n≤m⊔n

  ₁≤₃ : ∀ m n k → m ≤ m ⊕ n ⊕ k
  ₁≤₃ m n k = ₁≤₂ _ _

  ₂≤₃ : ∀ m n k → n ≤ m ⊕ n ⊕ k
  ₂≤₃ m n k = ≤-trans (₁≤₂ n k) (₂≤₂ m (n ⊔ k))

  ₃≤₃ : ∀ m n k → k ≤ m ⊕ n ⊕ k
  ₃≤₃ m n k = ≤-trans (₂≤₂ n k) (₂≤₂ m (n ⊔ k))

  ₁≤₄ : ∀ n₁ n₂ n₃ n₄ → n₁ ≤ n₁ ⊕ n₂ ⊕ n₃ ⊕ n₄
  ₁≤₄ n₁ n₂ n₃ n₄ = ₁≤₂ _ _

  ₂≤₄ : ∀ n₁ n₂ n₃ n₄ → n₂ ≤ n₁ ⊕ n₂ ⊕ n₃ ⊕ n₄
  ₂≤₄ n₁ n₂ n₃ n₄ = ₂≤₃ n₁ n₂ (n₃ ⊔ n₄)

  ₃≤₄ : ∀ n₁ n₂ n₃ n₄ → n₃ ≤ n₁ ⊕ n₂ ⊕ n₃ ⊕ n₄
  ₃≤₄ n₁ n₂ n₃ n₄ = ≤-trans (₁≤₂ n₃ n₄) (₃≤₃ n₁ n₂ (n₃ ⊔ n₄))

  ₄≤₄ : ∀ n₁ n₂ n₃ n₄ → n₄ ≤ n₁ ⊕ n₂ ⊕ n₃ ⊕ n₄
  ₄≤₄ n₁ n₂ n₃ n₄ = ≤-trans (₂≤₂ n₃ n₄) (₃≤₃ n₁ n₂ (n₃ ⊔ n₄))

size-ok TCTX-Empty = 0
size-ok (TCTX-Bind prevOk τδ) = suc (size-ok prevOk ⊕ size-twf τδ)

size-twf (TWF-TrueRef gok) = suc (size-ok gok)
size-twf (TWF-Base ε₁δ ε₂δ) = suc (size-t ε₁δ ⊕ size-t ε₂δ)
size-twf (TWF-Conj ρ₁δ ρ₂δ) = suc (size-twf ρ₁δ ⊕ size-twf ρ₂δ)
size-twf (TWF-Arr argδ resδ) = suc (size-twf argδ ⊕ size-twf resδ)
size-twf (TWF-ADT consδs) = suc (size-all-cons consδs)

size-all-cons [] = 0
size-all-cons (px ∷ pxs) = suc (size-twf px ⊕ size-all-cons pxs)

size-t (T-Unit gok) = suc (suc (size-ok gok))
size-t (T-Var gok _) = suc (size-ok gok)
size-t (T-Abs arrδ bodyδ) = suc (size-twf arrδ ⊕ size-t bodyδ)
size-t (T-App δ₁ δ₂ _ resτδ) = suc (size-t δ₁ ⊕ size-t δ₂ ⊕ size-twf resτδ)
size-t (T-Case resδ scrutτδ branches) = suc (size-t scrutτδ ⊕ size-twf resδ ⊕ size-bs branches)
size-t (T-Con _ conArg adtτ) = suc (size-t conArg ⊕ size-twf adtτ)
size-t (T-SubW <: εδ) = suc (size-t εδ ⊕ size-<: <:)

size-<: (ST-Base _) = 0
size-<: (ST-Arr sub₁ sub₂ δτ₁⇒τ₂ δτ₁') = suc (size-<: sub₁ ⊕ size-<: sub₂ ⊕ size-twf δτ₁⇒τ₂ ⊕ size-twf δτ₁')

size-bs NoBranches = 0
size-bs (OneMoreBranch εδ rest) = suc (size-t εδ ⊕ size-bs rest)
