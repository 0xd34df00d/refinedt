{-# OPTIONS --safe #-}

module Translation.Untyped.Lemmas.SubstCommutativity where

open import Data.Vec using (_∷_; [])
open import Data.Fin using (zero; suc)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Common.Helpers
open import Core.Syntax as C renaming (Γ to Γᶜ)
open import Core.Syntax.Derived as C
open import Core.Syntax.Derived.Substitution as CS
import      Core.Syntax.Renaming as CR
open import Core.Syntax.Substitution as CS
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; ε to εˢ)
import      Surface.Syntax.Renaming as SR
open import Surface.Syntax.Substitution as SS

open import Translation.Untyped
open import Translation.Untyped.Lemmas.Misc
import      Translation.Untyped.Lemmas.RenamingCommutativity as TURC

μ-ε-untyped-ext-commute : (f : Fin ℓ → STerm ℓ')
                        → μ-ε-untyped ∘ SS.ext f f≡ CS.ext (μ-ε-untyped ∘ f)
μ-ε-untyped-ext-commute f zero = refl
μ-ε-untyped-ext-commute f (suc ι) = TURC.μ-ε-act-commute suc (f ι)

act-id-on-μ-b-untyped : ∀ (f : Fin ℓ → CExpr ℓ') b
                      → CS.act-ε f (μ-b-untyped b) ≡ μ-b-untyped b
act-id-on-μ-b-untyped _ BUnit = refl

mutual
  μ-ρ-commute : (f : Fin ℓ → STerm ℓ')
              → (ρ : Refinement ℓ)
              → μ-ρ-untyped (SS.act-ρ f ρ) ≡ CS.act-ε (μ-ε-untyped ∘ f) (μ-ρ-untyped ρ)
  μ-ρ-commute f (ε₁ ≈ ε₂ of τ)
    rewrite CS.act-≡̂-commutes (μ-ε-untyped ∘ f) (μ-ε-untyped ε₁) (μ-ε-untyped ε₂) (μ-τ-untyped τ)
          | μ-ε-commute f ε₁
          | μ-ε-commute f ε₂
          | μ-τ-commute f τ
          = refl
  μ-ρ-commute f (ρ₁ ∧ ρ₂)
    rewrite act-×-commutes (μ-ε-untyped ∘ f) (μ-ρ-untyped ρ₁) (μ-ρ-untyped ρ₂)
          | μ-ρ-commute f ρ₁
          | μ-ρ-commute f ρ₂
          = refl
  μ-ρ-commute f Τ = refl

  common-ρ-steps : ∀ (f : Fin ℓ → STerm ℓ') b ρ
                 → Σ[ μ-b-untyped b ] CLam (μ-b-untyped b) (μ-ρ-untyped (SS.act-ρ (SS.ext f) ρ))
                   ≡
                   CS.act-ε (μ-ε-untyped ∘ f) (Σ[ μ-b-untyped b ] CLam (μ-b-untyped b) (μ-ρ-untyped ρ))
  common-ρ-steps f b ρ = step₁ then step₂ then step₃
    where
    fᶜ = μ-ε-untyped ∘ f

    step₁ : Σ[ μ-b-untyped b ] CLam (μ-b-untyped b) (μ-ρ-untyped (SS.act-ρ (SS.ext f) ρ))
            ≡
            Σ[ μ-b-untyped b ] CLam (μ-b-untyped b) (CS.act-ε (CS.ext fᶜ) (μ-ρ-untyped ρ))
    step₁ = cong
              (λ ε → Σ[ μ-b-untyped b ] CLam (μ-b-untyped b) ε)
              (μ-ρ-commute (SS.ext f) ρ
          then CS.act-ε-extensionality (μ-ε-untyped-ext-commute f) (μ-ρ-untyped ρ))

    step₂ : Σ[ μ-b-untyped b ] CLam (μ-b-untyped b) (CS.act-ε (CS.ext fᶜ) (μ-ρ-untyped ρ))
            ≡
            Σ[ CS.act-ε fᶜ (μ-b-untyped b) ] CLam (CS.act-ε fᶜ (μ-b-untyped b)) (CS.act-ε (CS.ext fᶜ) (μ-ρ-untyped ρ))
    step₂ rewrite act-id-on-μ-b-untyped fᶜ b = refl

    step₃ : Σ[ CS.act-ε fᶜ (μ-b-untyped b) ] CLam (CS.act-ε fᶜ (μ-b-untyped b)) (CS.act-ε (CS.ext fᶜ) (μ-ρ-untyped ρ))
            ≡
            CS.act-ε fᶜ (Σ[ μ-b-untyped b ] CLam (μ-b-untyped b) (μ-ρ-untyped ρ))
    step₃ rewrite act-Σ-commutes fᶜ (μ-b-untyped b) (CLam (μ-b-untyped b) (μ-ρ-untyped ρ)) = refl

  μ-τ-commute : (f : Fin ℓ → STerm ℓ')
              → (τˢ : SType ℓ)
              → μ-τ-untyped (SS.act-τ f τˢ) ≡ CS.act-ε (μ-ε-untyped ∘ f) (μ-τ-untyped τˢ)
  μ-τ-commute f ⟨ BUnit ∣ Τ ⟩ = refl
  μ-τ-commute f ⟨ b ∣ ρ@(_ ≈ _ of _) ⟩ = common-ρ-steps f b ρ
  μ-τ-commute f ⟨ b ∣ ρ@(_ ∧ _) ⟩ = common-ρ-steps f b ρ
  μ-τ-commute f (τ₁ ⇒ τ₂)
    rewrite μ-τ-commute f τ₁
          | μ-τ-commute (SS.ext f) τ₂
          | CS.act-ε-extensionality (μ-ε-untyped-ext-commute f) (μ-τ-untyped τ₂)
          = refl
  μ-τ-commute f (⊍ cons) rewrite μ-cons-commute f cons = refl

  μ-ε-commute : (f : Fin ℓ → STerm ℓ')
              → (εˢ : STerm ℓ)
              → μ-ε-untyped (SS.act-ε f εˢ) ≡ CS.act-ε (μ-ε-untyped ∘ f) (μ-ε-untyped εˢ)
  μ-ε-commute ε = {! !}

  μ-cons-commute : (f : Fin ℓ → STerm ℓ')
                 → (cons : S.ADTCons nₐ ℓ)
                 → μ-cons-untyped (SS.act-cons f cons) ≡ CS.act-cons (μ-ε-untyped ∘ f) (μ-cons-untyped cons)
  μ-cons-commute f [] = refl
  μ-cons-commute f (τ ∷ cons)
    rewrite μ-τ-commute f τ
          | μ-cons-commute f cons
          = refl
