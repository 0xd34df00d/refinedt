{-# OPTIONS --safe #-}

module Surface.WellScoped.CtxSuffix where

open import Data.Nat public using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties using (+-suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Surface.WellScoped
open import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.Substitution as S

infixl 5 _,_
data CtxSuffix (ℓ : ℕ) : (k : ℕ) → Set where
  ⊘   : CtxSuffix ℓ zero
  _,_ : (Δ : CtxSuffix ℓ k)
      → (τ : SType (k + ℓ))
      → CtxSuffix ℓ (suc k)

infixl 4 _++_
_++_ : Ctx ℓ → CtxSuffix ℓ k → Ctx (k + ℓ)
Γ ++ ⊘ = Γ
Γ ++ (Δ , τ) = (Γ ++ Δ) , τ

variable
  Δ : CtxSuffix ℓ k

-- We only ever need to substitute on whole context suffixes,
-- so there's no point in making this operator ternary and passing the index explicilty:
-- it is always equal to the length of the suffix.
[↦Δ_]_ : (ε : STerm ℓ)
       → CtxSuffix (suc ℓ) k
       → CtxSuffix ℓ k
[↦Δ ε ] ⊘ = ⊘
[↦Δ_]_ {k = suc k} ε (Δ , τ) = let τ' = subst SType (+-suc _ _) τ in [↦Δ ε ] Δ , [ ctx-idx k ↦τ weaken-ε-k k ε ] τ'
