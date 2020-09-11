module Surface.Derivations.WF where

open import Data.Nat.Base

open import Surface.Derivations
open import Surface.Syntax

size-ok  : Γ ok         → ℕ
size-twf : Γ ⊢ τ        → ℕ
size-t   : Γ ⊢ ε ⦂ τ    → ℕ
size-st  : Γ ⊢ τ₁ <: τ₂ → ℕ

infixl 20 _<>_
_<>_ : ℕ → ℕ → ℕ
_<>_ = _⊔_

size-ok TCTX-Empty = 0
size-ok (TCTX-Bind prevOk τδ) = suc (size-ok prevOk <> size-twf τδ)

size-twf (TWF-TrueRef gok) = suc (size-ok gok)
size-twf (TWF-Base ε₁δ ε₂δ) = suc (size-t ε₁δ <> size-t ε₂δ)
size-twf (TWF-Conj ρ₁δ ρ₂δ) = suc (size-twf ρ₁δ <> size-twf ρ₂δ)
size-twf (TWF-Arr argδ resδ) = suc (size-twf argδ <> size-twf resδ)
size-twf (TWF-ADT consδs) = suc (size-cons consδs)
  where
    size-cons : {cons : ADTCons n} → All (Γ ⊢_) cons → ℕ
    size-cons [] = zero
    size-cons (px ∷ pxs) = size-twf px <> size-cons pxs

size-t (T-Unit gok) = suc (size-ok gok)
size-t (T-Var gok _) = suc (size-ok gok)
size-t (T-Abs arrδ bodyδ) = suc (size-twf arrδ <> size-t bodyδ)
size-t (T-App δ₁ δ₂) = suc (size-t δ₁ <> size-t δ₂)
size-t (T-Case resδ scrutτδ branches) = suc (size-twf resδ <> size-t scrutτδ <> size-bs branches)
  where
    size-bs : ∀ {τ cons} {bs : CaseBranches n} → BranchesHaveType Γ cons bs τ → ℕ
    size-bs NoBranches = 0
    size-bs (OneMoreBranch εδ rest) = size-t εδ <> size-bs rest
size-t (T-Con conArg adtτ) = suc (size-t conArg <> size-twf adtτ)
size-t (T-Sub δ sub) = suc (size-t δ <> size-st sub)

size-st (ST-Base _ _) = 0
size-st (ST-Arr sub₁ sub₂) = suc (size-st sub₁ <> size-st sub₂)
