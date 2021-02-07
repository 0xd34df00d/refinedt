{-# OPTIONS --safe #-}

module Surface.WellScoped.CtxSuffix where

open import Data.Fin.Base using (suc; raise)
open import Data.Nat public using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Common.Helpers
open import Surface.WellScoped
open import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.Substitution as S
open import Surface.WellScoped.Membership

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

-- Green slime, so much green slime
private
  suffix-as-⊂' : (Δ : CtxSuffix ℓ k)
               → Γ' ≡ (Γ ++ Δ)
               → Γ ⊂ Γ'
  suffix-as-⊂' ⊘ refl = ⊂-refl
  suffix-as-⊂' (Δ , τ) refl = ignore-head (suffix-as-⊂' Δ refl)

  suffix-is-raise' : (Δ : CtxSuffix ℓ k)
                   → (eq-prf : Γ' ≡ (Γ ++ Δ))
                   → raise k f≡ _⊂_.ρ (suffix-as-⊂' Δ eq-prf)
  suffix-is-raise' ⊘ refl n = refl
  suffix-is-raise' (Δ , τ) refl n = cong suc (suffix-is-raise' Δ refl n)

suffix-as-⊂ : (Δ : CtxSuffix ℓ k)
            → Γ ⊂ (Γ ++ Δ)
suffix-as-⊂ Δ = suffix-as-⊂' Δ refl

suffix-is-raise : (Δ : CtxSuffix ℓ k)
                → raise k f≡ _⊂_.ρ (suffix-as-⊂ Δ)
suffix-is-raise Δ = suffix-is-raise' Δ refl

suffix-weakening-ε : (Δ : CtxSuffix ℓ k)
                   → weaken-ε-k k f≡  R.act-ε (_⊂_.ρ (suffix-as-⊂ Δ))
suffix-weakening-ε Δ = R.act-ε-extensionality (suffix-is-raise Δ)

suffix-weakening-τ : (Δ : CtxSuffix ℓ k)
                   → weaken-τ-k k f≡  R.act-τ (_⊂_.ρ (suffix-as-⊂ Δ))
suffix-weakening-τ Δ = R.act-τ-extensionality (suffix-is-raise Δ)
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
