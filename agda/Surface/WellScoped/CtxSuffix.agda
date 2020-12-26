{-# OPTIONS --safe #-}

module Surface.WellScoped.CtxSuffix where

open import Data.Nat public using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.WellScoped

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
