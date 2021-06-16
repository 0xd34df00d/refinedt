{-# OPTIONS --safe #-}

module Surface.Theorems.Agreement.TypeWellFormedness.WF where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.Membership
open import Surface.Derivations

infixr 20 _⊕_
_⊕_ : ℕ → ℕ → ℕ
_⊕_ = _⊔_

abstract
  m≤m⊕n : ∀ m n → m ≤ m ⊕ n
  m≤m⊕n = m≤m⊔n

  n≤m⊕n : ∀ m n → n ≤ m ⊕ n
  n≤m⊕n = n≤m⊔n

  m≤m⊕n⊕k : ∀ m n k → m ≤ m ⊕ n ⊕ k
  m≤m⊕n⊕k m n k = m≤m⊕n m (n ⊔ k)

  n≤m⊕n⊕k : ∀ m n k → n ≤ m ⊕ n ⊕ k
  n≤m⊕n⊕k m n k = ≤-trans (m≤m⊕n n k) (n≤m⊕n m (n ⊔ k))

  k≤m⊕n⊕k : ∀ m n k → k ≤ m ⊕ n ⊕ k
  k≤m⊕n⊕k m n k = ≤-trans (n≤m⊕n n k) (n≤m⊕n m (n ⊔ k))

mutual
  size-ok : Γ ok
          → ℕ
  size-ok TCTX-Empty = 0
  size-ok (TCTX-Bind prevOk τδ) = suc (size-ok prevOk ⊕ size-twf τδ)

  size-twf : Γ ⊢ τ
           → ℕ
  size-twf (TWF-TrueRef gok) = suc (size-ok gok)
  size-twf (TWF-Base ε₁δ ε₂δ) = suc (size-t ε₁δ ⊕ size-t ε₂δ)
  size-twf (TWF-Conj ρ₁δ ρ₂δ) = suc (size-twf ρ₁δ ⊕ size-twf ρ₂δ)
  size-twf (TWF-Arr argδ resδ) = suc (size-twf argδ ⊕ size-twf resδ)
  size-twf (TWF-ADT consδs) = suc (size-all-cons consδs)

  size-all-cons : {cons : ADTCons nₐ ℓ} → All (Γ ⊢_) cons → ℕ
  size-all-cons [] = 0
  size-all-cons (px ∷ pxs) = suc (size-twf px ⊕ size-all-cons pxs)

  size-∈ : Γ ok
         → τ ∈ Γ at ι
         → ℕ
  size-∈ (TCTX-Bind Γok τδ) (∈-zero refl) = suc (size-ok Γok ⊕ size-twf τδ)
  size-∈ (TCTX-Bind Γok τδ) (∈-suc refl ∈) = suc ((size-ok Γok ⊕ size-twf τδ) ⊕ size-∈ Γok ∈)

  size-t : Γ ⊢ ε ⦂ τ
         → ℕ
  size-t (T-Unit gok) = suc (suc (size-ok gok))
  size-t (T-Var gok ∈-prf) = suc (size-ok gok ⊕ size-∈ gok ∈-prf)
  size-t (T-Abs arrδ bodyδ) = suc (size-twf arrδ ⊕ size-t bodyδ)
  size-t (T-App δ₁ δ₂) = suc (size-t δ₁ ⊕ size-t δ₂)
  size-t (T-Case resδ scrutτδ branches) = suc (size-t scrutτδ ⊕ size-twf resδ ⊕ size-bs branches)
  size-t (T-Con _ conArg adtτ) = suc (size-t conArg ⊕ size-twf adtτ)
  size-t (T-Sub δ superδ sub) = suc (size-t δ ⊕ size-twf superδ ⊕ size-st sub)
  size-t (T-RConv εδ τ'δ _) = suc (size-t εδ ⊕ size-twf τ'δ)

  size-st : Γ ⊢ τ₁ <: τ₂
          → ℕ
  size-st (ST-Base _ _) = 0
  size-st (ST-Arr sub₁ sub₂) = suc (size-st sub₁ ⊕ size-st sub₂)

  size-bs : ∀ {τ cons} {bs : CaseBranches nₐ ℓ}
          → BranchesHaveType Γ cons bs τ
          → ℕ
  size-bs NoBranches = 0
  size-bs (OneMoreBranch εδ rest) = suc (size-t εδ ⊕ size-bs rest)

-- Properties
size-ok-≤-size-∈ : (Γok : Γ ok)
                 → (∈ : τ ∈ Γ at ι)
                 → size-ok Γok ≤ size-∈ Γok ∈
size-ok-≤-size-∈ (TCTX-Bind Γok τδ) (∈-zero refl) = s≤s ≤-refl
size-ok-≤-size-∈ (TCTX-Bind Γok τδ) (∈-suc refl ∈) = s≤s (m≤m⊔n _ _)
