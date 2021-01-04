{-# OPTIONS --safe #-}

module Surface.Derivations.WF where

open import Data.Nat.Base using (_⊔_; _≤_)
open import Data.Nat.Properties

open import Surface.Derivations
open import Surface.WellScoped

size-ok  : Γ ok         → ℕ
size-twf : Γ ⊢ τ        → ℕ
size-t   : Γ ⊢ ε ⦂ τ    → ℕ
size-st  : Γ ⊢ τ₁ <: τ₂ → ℕ
size-bs  : ∀ {τ cons} {bs : CaseBranches nₐ ℓ}
         → BranchesHaveType Γ cons bs τ
         → ℕ
size-all-cons : {cons : ADTCons nₐ ℓ} → All (Γ ⊢_) cons → ℕ

infixr 20 _<>_
_<>_ : ℕ → ℕ → ℕ
_<>_ = _⊔_

abstract
  m≤m<>n : ∀ m n → m ≤ m <> n
  m≤m<>n = m≤m⊔n

  n≤m<>n : ∀ m n → n ≤ m <> n
  n≤m<>n = n≤m⊔n

  m≤m<>n<>k : ∀ m n k → m ≤ m <> n <> k
  m≤m<>n<>k m n k = m≤m<>n m (n ⊔ k)

  n≤m<>n<>k : ∀ m n k → n ≤ m <> n <> k
  n≤m<>n<>k m n k = ≤-trans (m≤m<>n n k) (n≤m<>n m (n ⊔ k))

  k≤m<>n<>k : ∀ m n k → k ≤ m <> n <> k
  k≤m<>n<>k m n k = ≤-trans (n≤m<>n n k) (n≤m<>n m (n ⊔ k))

size-ok TCTX-Empty = 0
size-ok (TCTX-Bind prevOk τδ) = suc (size-ok prevOk <> size-twf τδ)

size-twf (TWF-TrueRef gok) = suc (size-ok gok)
size-twf (TWF-Base ε₁δ ε₂δ) = suc (size-t ε₁δ <> size-t ε₂δ)
size-twf (TWF-Conj ρ₁δ ρ₂δ) = suc (size-twf ρ₁δ <> size-twf ρ₂δ)
size-twf (TWF-Arr argδ resδ) = suc (size-twf argδ <> size-twf resδ)
size-twf (TWF-ADT consδs) = suc (size-all-cons consδs)

size-all-cons [] = 0
size-all-cons (px ∷ pxs) = suc (size-twf px <> size-all-cons pxs)

size-t (T-Unit gok) = suc (size-ok gok)
size-t (T-Var gok _) = suc (size-ok gok)
size-t (T-Abs arrδ bodyδ) = suc (size-twf arrδ <> size-t bodyδ)
size-t (T-App δ₁ δ₂) = suc (size-t δ₁ <> size-t δ₂)
size-t (T-Case resδ scrutτδ branches) = suc (size-t scrutτδ <> size-twf resδ <> size-bs branches)
size-t (T-Con _ conArg adtτ) = suc (size-t conArg <> size-twf adtτ)
size-t (T-Sub δ superδ sub) = suc (size-t δ <> size-twf superδ <> size-st sub)
size-t (T-RConv εδ τ'δ _) = suc (size-t εδ <> size-twf τ'δ)

size-st (ST-Base _ _) = 0
size-st (ST-Arr sub₁ sub₂) = suc (size-st sub₁ <> size-st sub₂)

size-bs NoBranches = 0
size-bs (OneMoreBranch εδ rest) = suc (size-t εδ <> size-bs rest)
