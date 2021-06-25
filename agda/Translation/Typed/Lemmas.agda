{-# OPTIONS --safe #-}

module Translation.Typed.Lemmas where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Syntax as C
open import Core.Syntax.Derived as C
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; ε to εˢ)
open import Surface.Derivations as S
open import Translation.Untyped
open import Translation.Typed

μ-b≡μ-τ[Γ⊢b] : (δ : Γˢ ⊢ ⟨ b ∣ Τ ⟩)
             → ⌊μ⌋-b b ≡ μ-τ δ
μ-b≡μ-τ[Γ⊢b] {b = BUnit} (TWF-TrueRef _) = refl
