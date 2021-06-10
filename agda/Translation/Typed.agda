{-# OPTIONS --safe #-}

module Translation.Typed where

open import Data.Vec using (_∷_; [])

open import Core.Syntax as C
open import Core.Syntax.Derived as C
open import Core.Derivations as C
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; ε to εˢ)
open import Surface.Derivations as S renaming (_⊢_⦂_ to _⊢ˢ_⦂_)

open import Translation.Untyped

mutual
  μ-τ : {τ : SType ℓ}
      → Γˢ ⊢ τ
      → CExpr ℓ
  μ-τ (TWF-TrueRef {b = b} Γok) = ⌊μ⌋-b b
  μ-τ (TWF-Base {b = b} δε₁ δε₂) = Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) (μ-ε δε₁ ≡̂ μ-ε δε₂ of ⌊μ⌋-b b)
  μ-τ (TWF-Conj δ₁ δ₂) = ⟨ μ-τ δ₁ × μ-τ δ₂ ⟩
  μ-τ (TWF-Arr δτ₁ δτ₂) = CΠ (μ-τ δτ₁) (μ-τ δτ₂)
  μ-τ (TWF-ADT consδs) = CADT (μ-cons consδs)

  μ-ε : ∀ {ε : STerm ℓ} {τ}
      → Γˢ ⊢ˢ ε ⦂ τ
      → CExpr ℓ
  μ-ε δε = {! δε !}

  μ-cons : {cons : S.ADTCons nₐ ℓ}
         → All (Γˢ ⊢_) cons
         → C.ADTCons nₐ ℓ
  μ-cons [] = []
  μ-cons (τ ∷ cons) = μ-τ τ ∷ μ-cons cons
