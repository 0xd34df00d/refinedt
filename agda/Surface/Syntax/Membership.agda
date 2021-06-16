{-# OPTIONS --safe #-}

module Surface.Syntax.Membership where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Data.Fin.Extra
open import Surface.Syntax
open import Surface.Syntax.Renaming as R
open import Surface.Syntax.Substitution as S

infix 4 _∈_at_
data _∈_at_ : SType ℓ → Ctx ℓ → Fin ℓ → Set where
  ∈-zero : (≡-prf : τ₀ ≡ R.weaken-τ τ)
         → τ₀ ∈ Γ , τ at zero
  ∈-suc  : (≡-prf : τ₀ ≡ R.weaken-τ τ)
         → (there : τ ∈ Γ at ι)
         → τ₀ ∈ Γ , τ' at suc ι

∈-injective : τ₁ ∈ Γ at ι
            → τ₂ ∈ Γ at ι
            → τ₁ ≡ τ₂
∈-injective (∈-zero refl) (∈-zero refl) = refl
∈-injective (∈-suc refl ∈₁) (∈-suc refl ∈₂) rewrite ∈-injective ∈₁ ∈₂ = refl

infix 4 _⊂_
record _⊂_ {ℓ ℓ'} (Γ : Ctx ℓ) (Γ' : Ctx ℓ') : Set where
  constructor MkTR
  field
    ρ      : Fin ℓ → Fin ℓ'
    ρ-∈    : τ ∈ Γ at ι
           → R.act-τ ρ τ ∈ Γ' at ρ ι
    ρ-mono : Monotonic ρ

append-both : ∀ {Γ : Ctx ℓ} {Γ' : Ctx ℓ'} {τ₀ : SType ℓ}
            → (Γ⊂Γ' : Γ ⊂ Γ')
            → Γ , τ₀ ⊂ Γ' , R.act-τ (_⊂_.ρ Γ⊂Γ') τ₀
append-both {Γ = Γ} {Γ' = Γ'} (MkTR ρ ρ-∈ ρ-mono) = MkTR (R.ext ρ) ρ-∈' (R.ext-monotonic ρ-mono)
  where
    ρ-∈' : τ ∈ Γ , τ' at ι
         → R.act-τ (R.ext ρ) τ ∈ Γ' , R.act-τ ρ τ' at R.ext ρ ι
    ρ-∈' {τ' = τ'} (∈-zero refl) rewrite R.weaken-τ-comm ρ τ' = ∈-zero refl
    ρ-∈' (∈-suc {τ = τ} refl there) rewrite R.weaken-τ-comm ρ τ = ∈-suc refl (ρ-∈ there)

ignore-head : ∀ {Γ : Ctx ℓ} {Γ' : Ctx ℓ'}
            → Γ ⊂ Γ'
            → Γ ⊂ Γ' , τ
ignore-head {ℓ} {ℓ'} {Γ = Γ} {Γ' = Γ'} (MkTR ρ ρ-∈ ρ-mono) = MkTR ρ' ρ'-∈ ρ'-mono
  where
    ρ' : Fin ℓ → Fin (suc ℓ')
    ρ' n = suc (ρ n)

    ρ'-∈ : τ ∈ Γ at ι
         → R.act-τ ρ' τ ∈ Γ' , τ' at ρ' ι
    ρ'-∈ {τ = τ} τ∈Γ-at-ι rewrite sym (R.act-τ-distr ρ suc τ) = ∈-suc refl (ρ-∈ τ∈Γ-at-ι)

    ρ'-mono : Monotonic ρ'
    ρ'-mono x<y = <-suc (ρ-mono x<y)

⊂-refl : Γ ⊂ Γ
⊂-refl {Γ = Γ} = MkTR (λ z → z) ρ-∈ (λ z → z)
  where
    ρ-∈ : τ ∈ Γ at ι
        → R.act-τ (λ z → z) τ ∈ Γ at ι
    ρ-∈ {τ = τ} τ∈Γ-at-ι rewrite R.act-τ-id (λ _ → refl) τ = τ∈Γ-at-ι


infix 4 _ℕ-idx_∈_
data _ℕ-idx_∈_ : (k : ℕ) → SType ℓ → Ctx (suc k + ℓ) → Set where
  ∈-zero : zero ℕ-idx τ ∈ (Γ , τ)
  ∈-suc  : ∀ {Γ : Ctx (suc k + ℓ)} {τ' : SType (suc k + ℓ)}
         → k ℕ-idx τ ∈ Γ
         → suc k ℕ-idx τ ∈ (Γ , τ')


infix 4 _⊂'_
record _⊂'_ {ℓ ℓ'} (Γ : Ctx ℓ) (Γ' : Ctx ℓ') : Set where
  constructor MkTR
  field
    ρ      : Fin ℓ → Fin ℓ'
    ρ-∈    : τ ∈ Γ at ι
           → τ' ≡ R.act-τ ρ τ
           → ι' ≡ ρ ι
           → τ' ∈ Γ' at ι'
    ρ-mono : Monotonic ρ

⊂'⇒⊂ : Γ ⊂' Γ' → Γ ⊂ Γ'
⊂'⇒⊂ (MkTR ρ ρ-∈ ρ-mono) = MkTR ρ (λ z → ρ-∈ z refl refl) ρ-mono

⊂⇒⊂' : Γ ⊂ Γ' → Γ ⊂' Γ'
⊂⇒⊂' (MkTR ρ ρ-∈ ρ-mono) = MkTR ρ (λ where z refl refl → ρ-∈ z) ρ-mono
