{-# OPTIONS --safe #-}

module Core.Operational.Theorems where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Syntax
open import Core.Syntax.Injectivity
open import Core.Syntax.Renaming
open import Core.Operational

weaken-ε-CAppₗ : CApp ε₁↑ ε₂↑ ≡ weaken-ε ε
               → ∃[ ε₁ ] (ε₁↑ ≡ weaken-ε ε₁)
weaken-ε-CAppₗ {ε = CApp ε₁ ε₂} ≡-prf = ⟨ ε₁ , proj₁ (CApp-injective ≡-prf) ⟩

weaken-ε-CAppᵣ : CApp ε₁↑ ε₂↑ ≡ weaken-ε ε
               → ∃[ ε₂ ] (ε₂↑ ≡ weaken-ε ε₂)
weaken-ε-CAppᵣ {ε = CApp ε₁ ε₂} ≡-prf = ⟨ ε₂ , proj₂ (CApp-injective ≡-prf) ⟩

weaken-ε-CApp : CApp ε₁↑ ε₂↑ ≡ weaken-ε ε
              → ∃[ ε₁ ] ∃[ ε₂ ] (ε ≡ CApp ε₁ ε₂)
weaken-ε-CApp {ε = CApp _ _} ≡-prf = ⟨ _ , ⟨ _ , refl ⟩ ⟩

↝-weakened : ∀ ε₂
           → ε₁↑ ↝ ε₂↑
           → ε₂↑ ≡ weaken-ε ε₂
           → ∃[ ε' ] (ε₁↑ ≡ weaken-ε ε')
↝-weakened (CApp ε₁' ε₂') (CE-AppL ε₁↝ε₂'↑) refl with ↝-weakened ε₁' ε₁↝ε₂'↑ refl
... | ⟨ ε' , refl ⟩ = ⟨ CApp ε' ε₂' , refl ⟩
↝-weakened ε₂ (CE-AppR x ε₁↑↝ε₂↑) ≡-prf = {! !}
↝-weakened ε₂ CE-AppAbs ≡-prf = {! !}
↝-weakened ε₂ (CE-ADT ε₁↑↝ε₂↑) ≡-prf = {! !}
↝-weakened ε₂ (CE-CaseScrut ε₁↑↝ε₂↑) ≡-prf = {! !}
↝-weakened ε₂ (CE-CaseMatch x ι) ≡-prf = {! !}

=β-weakened : τ₁↑ =β τ₂↑
            → τ₂↑ ≡ weaken-ε τ₂
            → ∃[ τ₁ ] (τ₁↑ ≡ weaken-ε τ₁)
=β-weakened (=-witness τ τ₁↝⋆ε τ₂↝⋆τ) = {! !}
