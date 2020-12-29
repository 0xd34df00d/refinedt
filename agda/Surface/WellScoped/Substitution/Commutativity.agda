{-# OPTIONS --safe #-}

module Surface.WellScoped.Substitution.Commutativity where

open import Data.Nat.Base using (zero; suc)
open import Data.Fin.Base using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Fin.Extra
open import Surface.WellScoped
import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.Substitution
open import Surface.WellScoped.Substitution.Distributivity
open import Surface.WellScoped.Substitution.Stable

subst-commutes-var : ∀ ε (ε₂ : STerm (suc ℓ)) ι
                   → ∀ var → [ ι ↦ε ε ] [ zero ↦ε ε₂ ] (SVar var) ≡ [ zero ↦ε [ ι ↦ε ε ] ε₂ ] [ suc ι ↦ε R.weaken-ε ε ] (SVar var)
subst-commutes-var ε ε₂ zero zero = refl
subst-commutes-var ε ε₂ zero (suc var) with zero <>? var
... | less m<n rewrite <>?-< m<n = refl
... | equal refl rewrite replace-weakened-ε zero ([ zero ↦ε ε ] ε₂) ε
                       | R.act-ε-id (λ _ → refl) ε = refl
subst-commutes-var ε ε₂ (suc ι) zero = refl
subst-commutes-var ε ε₂ (suc ι) (suc var) with suc ι <>? var
... | less m<n rewrite <>?-< (m<n⇒0<n m<n)
                     | pred-always-same m<n (m<n⇒0<n m<n) = refl
... | equal refl rewrite replace-weakened-ε zero ([ suc ι ↦ε ε ] ε₂) ε
                       | R.act-ε-id (λ _ → refl) ε = refl
... | greater m>n = refl

subst-commutes-τ : ∀ ι ε ε₂ (τ : SType (suc (suc ℓ)))
                 → [ ι ↦τ ε ] [ zero ↦τ ε₂ ] τ ≡ [ zero ↦τ [ ι ↦ε ε ] ε₂ ] [ suc ι ↦τ R.weaken-ε ε ] τ
subst-commutes-τ ι ε ε₂ τ rewrite act-τ-distr (replace-at zero ε₂) (replace-at ι ε) τ
                                | act-τ-distr (replace-at (suc ι) (R.weaken-ε ε)) (replace-at zero ([ ι ↦ε ε ] ε₂)) τ
                                | act-τ-extensionality (subst-commutes-var ε ε₂ ι) τ
                                = refl

subst-commutes-ε : ∀ ι ε ε₂ (ε₀ : STerm (suc (suc ℓ)))
                 → [ ι ↦ε ε ] [ zero ↦ε ε₂ ] ε₀ ≡ [ zero ↦ε [ ι ↦ε ε ] ε₂ ] [ suc ι ↦ε R.weaken-ε ε ] ε₀
subst-commutes-ε ι ε ε₂ ε₀ rewrite act-ε-distr (replace-at zero ε₂) (replace-at ι ε) ε₀
                                 | act-ε-distr (replace-at (suc ι) (R.weaken-ε ε)) (replace-at zero ([ ι ↦ε ε ] ε₂)) ε₀
                                 | act-ε-extensionality (subst-commutes-var ε ε₂ ι) ε₀
                                 = refl
