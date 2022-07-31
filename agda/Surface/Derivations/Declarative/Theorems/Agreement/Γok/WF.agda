{-# OPTIONS --safe #-}

{-
This module defines a notion of the size of a derivation that is
strong enough to prove agreement lemmas yielding a witness of `Γ ok`,
but not strong enough to prove the lemma `Γ ⊢ ε ⦂ τ → Γ ⊢ τ`.
-}

module Surface.Derivations.Declarative.Theorems.Agreement.Γok.WF where

open import Data.Nat.Base using (_⊔_; _≤_)
open import Data.Nat.Properties

open import Common.WF public

open import Surface.Derivations.Declarative
open import Surface.Syntax

size-ok  : Γ ok[ θ ]         → ℕ
size-twf : Γ ⊢[ θ ] τ        → ℕ
size-t   : Γ ⊢[ θ ] ε ⦂ τ    → ℕ
size-bs  : ∀ {τ cons} {bs : CaseBranches nₐ ℓ}
         → BranchesHaveType θ Γ cons bs τ
         → ℕ
size-all-cons : {cons : ADTCons nₐ ℓ} → All (Γ ⊢[ θ ]_) cons → ℕ

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
size-t (T-App δ₁ δ₂) = suc (size-t δ₁ ⊕ size-t δ₂)
size-t (T-Case resδ scrutτδ branches) = suc (size-t scrutτδ ⊕ size-twf resδ ⊕ size-bs branches)
size-t (T-Con _ conArg adtτ) = suc (size-t conArg ⊕ size-twf adtτ)
size-t (T-Sub δ superδ _) = suc (size-t δ ⊕ size-twf superδ)

size-bs NoBranches = 0
size-bs (OneMoreBranch εδ rest) = suc (size-t εδ ⊕ size-bs rest)
