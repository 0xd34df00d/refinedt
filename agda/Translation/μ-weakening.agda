module Translation.μ-weakening where

open import Data.Fin using (zero; suc)
open import Data.Nat.Base
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Syntax as C renaming (Γ to Γᶜ; ε to εᶜ)
open import Core.Syntax.Renaming as CR
open import Core.Operational as C
open import Surface.Syntax as S renaming (Γ to Γˢ; Γ' to Γˢ'; τ to τˢ; τ' to τˢ'; ε to εˢ)
open import Surface.Syntax.Subcontext as S
open import Surface.Derivations as S
open import Surface.Theorems.Agreement.Γok.WF
open import Surface.Theorems.Thinning

open import Translation.Untyped
open import Translation.Typed

μ-τ-thinning↓-commutes : {Γˢ : S.Ctx (k + ℓ)}
                       → (Γ⊂Γ' : k by Γˢ ⊂' Γˢ')
                       → (Γ'ok : Γˢ' ok[ E ])
                       → (τδ : Γˢ ⊢[ E ] τˢ)
                       → (τδ↓ : Acc _<_ (size-twf τδ))
                       → μ-τ (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok τδ τδ↓) ≡ CR.weaken-ε (μ-τ τδ)
μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok (TWF-TrueRef _) _ = {! !}
μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok (TWF-Base ε₁δ ε₂δ) (acc rec) = {! !}
μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok (TWF-Conj τδ τδ₁) (acc rec) = {! !}
μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok (TWF-Arr τδ τδ₁) (acc rec) = {! !}
μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok (TWF-ADT consδs) (acc rec) = {! !}

μ-τ-thinning-commutes : {Γˢ : S.Ctx (k + ℓ)}
                      → (Γ⊂Γ' : k by Γˢ ⊂' Γˢ')
                      → (Γ'ok : Γˢ' ok[ E ])
                      → (τδ : Γˢ ⊢[ E ] τˢ)
                      → μ-τ (Γ⊢τ-thinning Γ⊂Γ' Γ'ok τδ) ≡ CR.weaken-ε (μ-τ τδ)
μ-τ-thinning-commutes Γ⊂Γ' Γ'ok τδ = μ-τ-thinning↓-commutes Γ⊂Γ' Γ'ok τδ (<-wellFounded _)

μ-τ-weakening-commutes : (Γok : Γˢ ok[ E ])
                       → (τ'δ : Γˢ ⊢[ E ] τˢ')
                       → (τδ : Γˢ ⊢[ E ] τˢ)
                       → μ-τ (Γ⊢τ-weakening Γok τ'δ τδ) ≡ CR.weaken-ε (μ-τ τδ)
μ-τ-weakening-commutes Γok τ'δ = μ-τ-thinning-commutes ignore-head (TCTX-Bind Γok τ'δ)
