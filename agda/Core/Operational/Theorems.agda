{-# OPTIONS --safe #-}

module Core.Operational.Theorems where

open import Data.Fin using (zero)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Syntax
open import Core.Syntax.Injectivity
open import Core.Syntax.Renaming as R
open import Core.Syntax.Substitution as S
open import Core.Operational

↝-weakened : ∀ ε₂
           → ε₁↑ ↝ ε₂↑
           → ε₂↑ ≡ weaken-ε ε₂
           → ∃[ ε' ] (ε₁↑ ≡ weaken-ε ε')
↝-weakened (CApp ε₁' ε₂') (CE-AppL ε₁↝ε₁'↑) refl with ↝-weakened ε₁' ε₁↝ε₁'↑ refl
... | ⟨ ε' , refl ⟩ = ⟨ CApp ε' ε₂' , refl ⟩
↝-weakened (CApp ϖ ε₂') (CE-AppR x ε₂↝ε₂'↑) refl with ↝-weakened ε₂' ε₂↝ε₂'↑ refl
... | ⟨ ε' , refl ⟩ = ⟨ CApp ϖ ε' , refl ⟩
↝-weakened ε₂ CE-AppAbs ≡-prf = {! !}
↝-weakened (CCon ι ε cons) (CE-ADT ε₁↑↝ε↑) refl with ↝-weakened ε ε₁↑↝ε↑ refl
... | ⟨ ε' , refl ⟩ = ⟨ CCon ι ε' cons , refl ⟩
↝-weakened (CCase ε branches) (CE-CaseScrut ε₁↑↝ε↑) refl with ↝-weakened ε ε₁↑↝ε↑ refl
... | ⟨ ε' , refl ⟩ = ⟨ CCase ε' branches , refl ⟩
↝-weakened ε₂ (CE-CaseMatch x ι) ≡-prf = {! !}

↝⋆-weakened : ∀ ε₂
            → ε₁↑ ↝⋆ ε₂↑
            → ε₂↑ ≡ weaken-ε ε₂
            → ∃[ ε' ] (ε₁↑ ≡ weaken-ε ε')
↝⋆-weakened ε₂ ε₁↑↝⋆ε₂↑ ≡-prf = {! !}

weakened-↝ : ∀ ε₁
           → ε₁↑ ↝ ε₂↑
           → ε₁↑ ≡ weaken-ε ε₁
           → ∃[ ε' ] (ε₂↑ ≡ weaken-ε ε')
weakened-↝ = {! !}

weakened-↝⋆ : ∀ ε₁
            → ε₁↑ ↝⋆ ε₂↑
            → ε₁↑ ≡ weaken-ε ε₁
            → ∃[ ε' ] (ε₂↑ ≡ weaken-ε ε')
weakened-↝⋆ = {! !}

=β-weakened : τ₁↑ =β τ₂↑
            → τ₂↑ ≡ weaken-ε τ₂
            → ∃[ τ₁ ] (τ₁↑ ≡ weaken-ε τ₁)
=β-weakened {τ₂ = τ₂} (=-witness τ τ₁↑↝⋆τ τ₂↑↝⋆τ) ≡-prf with weakened-↝⋆ τ₂ τ₂↑↝⋆τ ≡-prf
... | ⟨ τ' , refl ⟩ = ↝⋆-weakened τ' τ₁↑↝⋆τ refl
