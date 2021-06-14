module Surface.Theorems.Thinning.WF where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Surface.Syntax
open import Surface.Derivations
open import Surface.Derivations.WF
open import Surface.Theorems.Thinning
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Membership

twf-thinning-size : (Γ⊂Γ' : Γ ⊂ Γ')
                  → (Γ'ok : Γ' ok)
                  → (Γ⊢τ : Γ ⊢ τ)
                  → size-twf (twf-thinning Γ⊂Γ' Γ'ok Γ⊢τ) ≡ size-twf Γ⊢τ
twf-thinning-size Γ⊂Γ' Γ'ok Γ⊢τ = {! !}

twf-weakening-size : (Γok : Γ ok)
                   → (Γ⊢τ' : Γ ⊢ τ')
                   → (Γ⊢τ : Γ ⊢ τ)
                   → size-twf (twf-weakening Γok Γ⊢τ' Γ⊢τ) ≡ size-twf Γ⊢τ
twf-weakening-size Γok Γ⊢τ' Γ⊢τ = twf-thinning-size (ignore-head ⊂-refl) (TCTX-Bind Γok Γ⊢τ') Γ⊢τ
