{-# OPTIONS --safe #-}

module Intermediate.Syntax.Substitution.Stable where

open import Data.Fin using (Fin; suc; zero; raise)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Helpers
open import Data.Fin.Extra

open import Intermediate.Syntax
open import Intermediate.Syntax.Substitution as S
open import Intermediate.Syntax.Substitution.FromRenaming
open import Intermediate.Syntax.Substitution.Distributivity
import Intermediate.Syntax.Renaming as R

k-<-x+k : ∀ k (x : Fin ℓ)
        → ctx-idx {ℓ} k < raise (suc k) x
k-<-x+k zero x = <-zero x
k-<-x+k (suc k) x = <-suc (k-<-x+k k x)

replace-too-far : ∀ k (ε : ITerm (k + ℓ))
                → ∀ x
                → replace-at (ctx-idx k) ε (raise (suc k) x) ≡ IVar (raise k x)
replace-too-far k ε x rewrite <>?-< (k-<-x+k k x) = refl

replace-weakened-τ : ∀ k (ε : ITerm (k + ℓ)) (σ : IType ℓ)
                   → [ ctx-idx k ↦τ ε ] (R.weaken-τ-k (suc k) σ) ≡ R.weaken-τ-k k σ
replace-weakened-τ k ε σ
  rewrite ρ-as-σ-τ (raise k) σ
        | σ-ρ-distr-τ (replace-at (ctx-idx k) ε) (raise (suc k)) σ
        | act-τ-extensionality (replace-too-far k ε) σ
        = refl

replace-weakened-τ-zero : ∀ (ε : ITerm ℓ) (σ : IType ℓ)
                        → [ zero ↦τ ε ] (R.weaken-τ σ) ≡ σ
replace-weakened-τ-zero ε σ
  rewrite replace-weakened-τ zero ε σ
        | R.act-τ-id (λ _ → refl) σ
        = refl

replace-weakened-ε : ∀ k (ε : ITerm (k + ℓ)) (ε₀ : ITerm ℓ)
                   → [ ctx-idx k ↦ε ε ] (R.weaken-ε-k (suc k) ε₀) ≡ R.weaken-ε-k k ε₀
replace-weakened-ε k ε ε₀
  rewrite ρ-as-σ-ε (raise k) ε₀
        | σ-ρ-distr-ε (replace-at (ctx-idx k) ε) (raise (suc k)) ε₀
        | act-ε-extensionality (replace-too-far k ε) ε₀
        = refl

replace-weakened-ε-zero : ∀ (ε ε₀ : ITerm ℓ)
                        → [ zero ↦ε ε ] (R.weaken-ε ε₀) ≡ ε₀
replace-weakened-ε-zero ε ε₀
  rewrite replace-weakened-ε zero ε ε₀
        | R.act-ε-id (λ _ → refl) ε₀
        = refl
