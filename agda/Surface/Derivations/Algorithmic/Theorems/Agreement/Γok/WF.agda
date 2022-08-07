{-# OPTIONS --safe #-}

{-
This module defines a notion of the size of a derivation that is
strong enough to prove agreement lemmas yielding a witness of `Γ ok`,
but not strong enough to prove the lemma `Γ ⊢ ε ⦂ τ → Γ ⊢ τ`.
-}

module Surface.Derivations.Algorithmic.Theorems.Agreement.Γok.WF where

open import Data.Fin using (#_)
open import Data.Nat.Base using (_⊔_; _≤_; _<_; s≤s)
open import Data.Nat.Properties
open import Data.Vec
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.WF public

open import Surface.Syntax
open import Surface.Derivations.Algorithmic

mutual
  size-ok : Γ ok[ θ , φ ]
          → ℕ
  size-ok TCTX-Empty = 0
  size-ok (TCTX-Bind Γok τδ) = suc (size-ok Γok ⊕ size-twf τδ)

  size-twf : Γ ⊢[ θ , φ ] τ
           → ℕ
  size-twf (TWF-TrueRef Γok) = suc (size-ok Γok)
  size-twf (TWF-Base ε₁δ ε₂δ) = suc (size-t ε₁δ ⊕ size-t ε₂δ)
  size-twf (TWF-Conj ρ₁δ ρ₂δ) = suc (size-twf ρ₁δ ⊕ size-twf ρ₂δ)
  size-twf (TWF-Arr argδ resδ) = suc (size-twf argδ ⊕ size-twf resδ)
  size-twf (TWF-ADT consδs) = suc (size-all-cons consδs)

  size-t : Γ ⊢[ θ , φ of κ ] ε ⦂ τ
         → ℕ
  size-t (T-Unit Γok) = suc (suc (size-ok Γok))
  size-t (T-Var Γok ∈) = suc (size-ok Γok)
  size-t (T-Abs εδ) = suc (size-t εδ)
  size-t (T-App ε₁δ ε₂δ _) = suc (size-t ε₁δ ⊕ size-t ε₂δ)
  size-t (T-Case resδ scrutτδ branches) = suc (size-t scrutτδ ⊕ size-twf resδ ⊕ size-bs branches)
  size-t (T-Con _ conArg adtτ) = suc (size-t conArg ⊕ size-twf adtτ)
  size-t (T-Sub εδ _) = suc (size-t εδ)

  size-bs  : ∀ {τ cons} {bs : CaseBranches nₐ ℓ}
           → BranchesHaveType θ φ Γ cons bs τ
           → ℕ
  size-bs NoBranches = 0
  size-bs (OneMoreBranch εδ rest) = suc (size-t εδ ⊕ size-bs rest)

  size-all-cons : {cons : ADTCons nₐ ℓ}
                → All (Γ ⊢[ θ , φ ]_) cons
                → ℕ
  size-all-cons [] = 0
  size-all-cons (px ∷ pxs) = suc (size-twf px ⊕ size-all-cons pxs)
