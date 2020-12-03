{-# OPTIONS --safe #-}

module Surface.WellScoped.Membership where

open import Data.Fin using (Fin; zero; suc)

open import Data.Fin.Extra
open import Surface.WellScoped
open import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.Substitution as S

infix 4 _∈_at_
data _∈_at_ : SType ℓ → Ctx ℓ → Fin ℓ → Set where
  ∈-zero : R.weaken-τ τ ∈ (Γ , τ) at zero
  ∈-suc  : τ ∈ Γ at idx
         → R.weaken-τ τ ∈ (Γ , τ') at suc idx

infix 4 _⊂_
record _⊂_ {ℓ ℓ'} (Γ : Ctx ℓ) (Γ' : Ctx ℓ') : Set where
  constructor MkTR
  field
    ρ      : Fin ℓ → Fin ℓ'
    ρ-∈    : τ ∈ Γ at idx
           → R.act-τ ρ τ ∈ Γ' at ρ idx
    ρ-mono : Monotonic ρ

append-both : ∀ {Γ : Ctx ℓ} {Γ' : Ctx ℓ'} {τ₀ : SType ℓ}
            → (Γ⊂Γ' : Γ ⊂ Γ')
            → Γ , τ₀ ⊂ Γ' , R.act-τ (_⊂_.ρ Γ⊂Γ') τ₀
append-both {Γ = Γ} {Γ' = Γ'} (MkTR ρ ρ-∈ ρ-mono) = MkTR (R.ext ρ) ρ-∈' (S.ext-monotonic ρ-mono)
  where
    ρ-∈' : τ ∈ Γ , τ' at idx
         → R.act-τ (R.ext ρ) τ ∈ Γ' , R.act-τ ρ τ' at R.ext ρ idx
    ρ-∈' {τ' = τ'} ∈-zero rewrite R.weaken-τ-comm ρ τ' = ∈-zero
    ρ-∈' (∈-suc {τ = τ} x) rewrite R.weaken-τ-comm ρ τ = ∈-suc (ρ-∈ x)

ignore-head : ∀ {Γ : Ctx ℓ}
            → Γ ⊂ Γ , τ
ignore-head = MkTR suc ∈-suc <-suc
