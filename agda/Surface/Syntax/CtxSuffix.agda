{-# OPTIONS --safe #-}

module Surface.Syntax.CtxSuffix where

open import Data.Fin.Base using (suc; raise)
open import Data.Nat public using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Common.Helpers
open import Surface.Syntax
open import Surface.Syntax.Renaming as R
open import Surface.Syntax.Substitution as S
open import Surface.Syntax.Membership

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


-- Non-empty suffix, useful for the substitution lemmas
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

∈-at-concat-point : (Δ : ,-CtxSuffix ℓ σ k)
                  → τ ∈ Γ ,σ, Δ at ctx-idx k
                  → τ ≡ R.weaken-τ-k (suc k) σ
∈-at-concat-point [ _ ] (∈-zero ≡-prf) = ≡-prf
∈-at-concat-point {σ = σ} {k = k} (Δ , τ) (∈-suc refl ∈)
  rewrite ∈-at-concat-point Δ ∈
        | weaken-τ-suc-k k σ
        = refl
