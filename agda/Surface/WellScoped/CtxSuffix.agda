{-# OPTIONS --safe #-}

module Surface.WellScoped.CtxSuffix where

open import Data.Nat public using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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



data ,-CtxSuffix (ℓ : ℕ) : (σ : SType ℓ) → (k : ℕ) → Set where
  [_] : ∀ σ
      → ,-CtxSuffix ℓ σ zero
  _,_ : (Δ : ,-CtxSuffix ℓ σ k)
      → (τ : SType (suc k + ℓ))
      → ,-CtxSuffix ℓ σ (suc k)

infixl 4 _,σ,_
_,σ,_ : Ctx ℓ → ,-CtxSuffix ℓ σ k → Ctx (suc k + ℓ)
Γ ,σ, [ σ ] = Γ , σ
Γ ,σ, (Δ , τ) = (Γ ,σ, Δ) , τ

-- We only ever need to substitute on whole context suffixes,
-- so there's no point in making this operator ternary and passing the index explicilty:
-- it is always equal to the length of the suffix.
[↦Δ_]_ : (ε : STerm ℓ)
       → ,-CtxSuffix ℓ σ k
       → CtxSuffix ℓ k
[↦Δ ε ] [ σ ] = ⊘
[↦Δ_]_ {k = .suc k} ε (Δ , τ) = [↦Δ ε ] Δ , [ ctx-idx k ↦τ weaken-ε-k _ ε ] τ
