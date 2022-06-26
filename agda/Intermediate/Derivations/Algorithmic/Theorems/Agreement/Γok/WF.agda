{-# OPTIONS --safe #-}

{-
This module defines a notion of the size of a derivation that is
strong enough to prove agreement lemmas yielding a witness of `Γ ok`,
but not strong enough to prove the lemma `Γ ⊢ ε ⦂ τ → Γ ⊢ τ`.
-}

module Intermediate.Derivations.Algorithmic.Theorems.Agreement.Γok.WF where

open import Data.Fin using (#_)
open import Data.Nat.Base using (_⊔_; _≤_; _<_; s≤s)
open import Data.Nat.Properties
open import Data.Vec
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.WF public

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
size-t (T-Con _ conArg (TWF-ADT consδs)) = suc (size-t conArg ⊕ size-all-cons consδs)
size-t (T-SubW <: εδ) = suc (size-t εδ ⊕ size-<: <:)

size-<: (ST-Base _ τ'δ τδ) = suc (size-twf τ'δ ⊕ size-twf τδ)
size-<: (ST-Arr sub₁ sub₂ τ₁⇒τ₂'δ τ₁'⇒τ₂δ) = suc (size-<: sub₁ ⊕ size-<: sub₂ ⊕ size-twf τ₁⇒τ₂'δ ⊕ size-twf τ₁'⇒τ₂δ)

size-bs NoBranches = 0
size-bs (OneMoreBranch εδ rest) = suc (size-t εδ ⊕ size-bs rest)

ST-Arr-size-vec : [ θ ] Γ ⊢ τ₁ ⇒ τ₂' <: τ₁' ⇒ τ₂
                → Vec ℕ 4
ST-Arr-size-vec (ST-Arr <:₁δ <:₂δ τ₁⇒τ₂'δ τ₁'⇒τ₂δ)
  = size-<: <:₁δ
  ∷ size-<: <:₂δ
  ∷ size-twf τ₁⇒τ₂'δ
  ∷ size-twf τ₁'⇒τ₂δ
  ∷ []

-- A trivial lemma that's a bit annoying to spell out and that'll be needed in a couple of other places
ST-Arr-τ₁'-smaller : ∀ {<:₁δ} {<:₂δ} {τ₁⇒τ₂'δ} {τ₁'δ : [ θ ] Γ ⊢ τ₁'} {τ₂δ}
                   → (<:δ : [ θ ] Γ ⊢ τ₁ ⇒ τ₂' <: τ₁' ⇒ τ₂)
                   → ⦃ <:δ ≡ ST-Arr <:₁δ <:₂δ τ₁⇒τ₂'δ (TWF-Arr τ₁'δ τ₂δ) ⦄
                   → size-twf τ₁'δ < size-<: <:δ
ST-Arr-τ₁'-smaller <:δ ⦃ refl ⦄ = ≤-trans (s≤s (≤-trans (₁≤₂ _ _) (n≤1+n _))) (<₄ (ST-Arr-size-vec <:δ) (# 3))
