{-# OPTIONS --safe #-}

module Surface.WellScoped.Substitution.Stable where

open import Data.Fin using (Fin; suc; zero; raise)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Fin.Extra
open import Surface.WellScoped
open import Surface.WellScoped.Substitution as S
open import Surface.WellScoped.Substitution.FromRenaming
open import Surface.WellScoped.Substitution.Distributivity
import Surface.WellScoped.Renaming as R

k-<-x+k : ∀ k (x : Fin ℓ)
        → ctx-idx {ℓ} k < raise (suc k) x
k-<-x+k zero x = <-zero x
k-<-x+k (suc k) x = <-suc (k-<-x+k k x)

replace-too-far : ∀ k (ε : STerm (k + ℓ))
                → ∀ x
                → replace-at (ctx-idx k) ε (raise (suc k) x) ≡ SVar (raise k x)
replace-too-far k ε x rewrite <>?-< (k-<-x+k k x) = refl

replace-weakened-τ : ∀ k (ε : STerm (k + ℓ)) (σ : SType ℓ)
                   → [ ctx-idx k ↦τ ε ] (R.weaken-τ-k (suc k) σ) ≡ R.weaken-τ-k k σ
replace-weakened-τ k ε σ rewrite ρ-as-σ-τ (raise k) σ
                               | σ-ρ-τ-distr (replace-at (ctx-idx k) ε) (raise (suc k)) σ
                               | act-τ-extensionality (replace-too-far k ε) σ
                               = refl
