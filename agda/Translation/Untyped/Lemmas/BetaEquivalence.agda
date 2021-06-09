{-# OPTIONS --safe #-}

module Translation.Untyped.Lemmas.BetaEquivalence where

open import Data.Fin using (zero)
open import Data.Vec using (Vec; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Syntax as C
open import Core.Operational as C renaming (_↝_ to _↝ᶜ_)
open import Core.Operational.BetaEquivalence as C
open import Surface.Syntax as S
open import Surface.Operational as S renaming (_↝_ to _↝ˢ_)
open import Surface.Operational.BetaEquivalence as S

open import Translation.Untyped
open import Translation.Untyped.Lemmas.SubstCommutativity

μ-ε-preserves-values : {ϖ : STerm ℓ}
                     → S.IsValue ϖ
                     → C.IsValue (μ-ε-untyped ϖ)
μ-ε-preserves-values IV-Abs = IV-Abs
μ-ε-preserves-values IV-Unit = IV-Abs
μ-ε-preserves-values (IV-ADT iv) = IV-ADT (μ-ε-preserves-values iv)

μ-ε-preserves-↝ : ∀ {ε ε' : STerm ℓ}
                → ε ↝ˢ ε'
                → μ-ε-untyped ε ↝ᶜ μ-ε-untyped ε'
μ-ε-preserves-↝ (E-AppL ε↝ε') = CE-AppL (μ-ε-preserves-↝ ε↝ε')
μ-ε-preserves-↝ (E-AppR iv ε↝ε') = CE-AppR (μ-ε-preserves-values iv) (μ-ε-preserves-↝ ε↝ε')
μ-ε-preserves-↝ (E-AppAbs {ϖ = ϖ} {ε = ε} iv)
  rewrite μ-ε-preserves-↦ zero ϖ ε
        = CE-AppAbs (μ-ε-preserves-values iv)
μ-ε-preserves-↝ (E-ADT ε↝ε') = CE-ADT (μ-ε-preserves-↝ ε↝ε')
μ-ε-preserves-↝ (E-CaseScrut ε↝ε') = CE-CaseScrut (μ-ε-preserves-↝ ε↝ε')
μ-ε-preserves-↝ (E-CaseMatch x ι) = {! !}

μ-τ-preserves-↝β : ∀ {τ τ' : SType ℓ}
                 → τ ↝βτ τ'
                 → μ-τ-untyped τ ↝β μ-τ-untyped τ'
μ-τ-preserves-↝β (↝βτ-Subst ι ε ε' τ ε↝ε')
  rewrite μ-τ-preserves-↦ ι ε' τ
        | μ-τ-preserves-↦ ι ε τ
        = ↝β-Subst ι (μ-ε-untyped ε) (μ-ε-untyped ε') (μ-τ-untyped τ) (μ-ε-preserves-↝ ε↝ε')

μ-τ-preserves-↭β : ∀ {τ₁ τ₂ : SType ℓ}
                 → τ₁ ↭βτ τ₂
                 → μ-τ-untyped τ₁ ↭β μ-τ-untyped τ₂
μ-τ-preserves-↭β (forward τ₁↝τ₂) = forward (μ-τ-preserves-↝β τ₁↝τ₂)
μ-τ-preserves-↭β (backward τ₂↝τ₁) = backward (μ-τ-preserves-↝β τ₂↝τ₁)
