{-# OPTIONS --safe #-}

module Surface.WellScoped.Substitution.Stable where

open import Data.Fin using (Fin; suc; zero; toℕ; raise)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Fin.Extra
open import Surface.WellScoped
open import Surface.WellScoped.Substitution as S
import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.FreeVars

RenamingAsSubst : {Ty : ℕ → Set} → R.ActionOn Ty → S.ActionOn Ty → Set
RenamingAsSubst {Ty} ρ-act σ-act = ∀ {ℓ ℓ'}
                                   → (ρ : Fin ℓ → Fin ℓ')
                                   → (v : Ty ℓ)
                                   → ρ-act ρ v ≡ σ-act (SVar ∘ ρ) v

var-ext-commutes : ∀ (ρ : Fin ℓ → Fin ℓ')
                 → ∀ x → SVar (R.ext ρ x) ≡ ext (SVar ∘ ρ) x
var-ext-commutes ρ zero = refl
var-ext-commutes ρ (suc x) = refl

ρ-as-σ-τ : RenamingAsSubst R.act-τ act-τ
ρ-as-σ-ρ : RenamingAsSubst R.act-ρ act-ρ
ρ-as-σ-ε : RenamingAsSubst R.act-ε act-ε

ρ-as-σ-τ ρ ⟨ b ∣ ρ' ⟩ rewrite ρ-as-σ-ρ (R.ext ρ) ρ'
                            | act-ρ-extensionality (var-ext-commutes ρ) ρ' = refl
ρ-as-σ-τ ρ (τ₁ ⇒ τ₂) rewrite ρ-as-σ-τ ρ τ₁
                           | ρ-as-σ-τ (R.ext ρ) τ₂
                           | act-τ-extensionality (var-ext-commutes ρ) τ₂ = refl
ρ-as-σ-τ ρ (⊍ cons) = {! !}

ρ-as-σ-ρ ρ ρ' = {! !}

ρ-as-σ-ε ρ ε = {! !}


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
                               | subst-rename-τ-distr (replace-at (ctx-idx k) ε) (raise (suc k)) σ
                               | act-τ-extensionality (replace-too-far k ε) σ
                               = refl
