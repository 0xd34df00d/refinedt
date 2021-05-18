{-# OPTIONS --safe #-}

module Core.Derivations.Theorems where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Syntax
open import Core.Syntax.Renaming as R
open import Core.Syntax.Substitution as S
open import Core.Derivations
open import Core.Operational

τ-unweaken : ∀ ε
           → Γ ⊢ ε↑ ⦂ τ↑
           → ε↑ ≡ weaken-ε ε
           → ∃[ τ ] (τ↑ ≡ weaken-ε τ)
τ-unweaken ε (CT-Var δ) ≡-prf = {! !}
τ-unweaken ε (CT-Weaken {τ₁ = τ₁} _ _) _ = ⟨ τ₁ , refl ⟩
τ-unweaken ε (CT-Form _ _) _ = ⟨ CSort _ , refl ⟩
τ-unweaken ε (CT-App δ δ₁) ≡-prf = {! !}
τ-unweaken ε (CT-Abs δ δ₁) ≡-prf = {! !}
τ-unweaken ε (CT-Conv εδ τ↑δ x) refl with τ-unweaken ε εδ refl
... | ⟨ τ , refl ⟩ = {! !}
τ-unweaken ε (CT-UnitType δ) ≡-prf = ⟨ CSort ⋆ , refl ⟩
τ-unweaken ε (CT-UnitTerm δ) ≡-prf = ⟨ CUnit , refl ⟩
τ-unweaken ε (CT-ADTForm consδs) ≡-prf = ⟨ CSort ⋆ , refl ⟩
τ-unweaken ε (CT-ADTCon ≡-prf₁ δ δ₁) ≡-prf = {! !}
τ-unweaken ε (CT-ADTCase δ δ₁ branches) ≡-prf = {! !}
