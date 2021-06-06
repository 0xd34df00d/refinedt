{-# OPTIONS --safe #-}

module Translation.Untyped.Lemmas.SubstCommutativity where

open import Data.Vec using (_∷_; [])
open import Data.Fin using (zero; suc)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Common.Helpers
open import Core.Syntax as C renaming (Γ to Γᶜ)
open import Core.Syntax.Derived as C
open import Core.Syntax.Derived.Renaming as CR
import Core.Syntax.Renaming as CR
open import Core.Syntax.Substitution as CS
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; ε to εˢ)
import Surface.Syntax.Renaming as SR
open import Surface.Syntax.Substitution as SS

open import Translation.Untyped
open import Translation.Untyped.Lemmas.RenamingCommutativity

μ-ε-untyped-ext-commute : (f : Fin ℓ → STerm ℓ')
                        → μ-ε-untyped ∘ SS.ext f f≡ CS.ext (μ-ε-untyped ∘ f)
μ-ε-untyped-ext-commute f zero = refl
μ-ε-untyped-ext-commute f (suc ι) = μ-ε-act-commute suc (f ι)

mutual
  μ-τ-commute : (f : Fin ℓ → STerm ℓ')
              → (τˢ : SType ℓ)
              → μ-τ-untyped (SS.act-τ f τˢ) ≡ CS.act-ε (μ-ε-untyped ∘ f) (μ-τ-untyped τˢ)
  μ-τ-commute f ⟨ BUnit ∣ Τ ⟩ = refl
  μ-τ-commute f ⟨ b ∣ ρ@(_ ≈ _ of _) ⟩ = {! !}
  μ-τ-commute f ⟨ b ∣ ρ@(_ ∧ _) ⟩ = {! !}
  μ-τ-commute f (τ₁ ⇒ τ₂)
    rewrite μ-τ-commute f τ₁
          | μ-τ-commute (SS.ext f) τ₂
          | CS.act-ε-extensionality (μ-ε-untyped-ext-commute f) (μ-τ-untyped τ₂)
          = refl
  μ-τ-commute f (⊍ cons) = {! !}
