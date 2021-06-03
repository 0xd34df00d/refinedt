-- {-# OPTIONS --safe #-}

module Translation.Untyped.Lemmas where

open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Helpers
open import Core.Syntax as C renaming (Γ to Γᶜ)
open import Core.Syntax.Derived as C
open import Core.Syntax.Derived.Actions as C
import Core.Syntax.Renaming as CR
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; ε to εˢ)
import Surface.Syntax.Renaming as SR

open import Translation.Untyped

exts-agree : (f : Fin ℓ → Fin ℓ')
           → SR.ext f f≡ CR.ext f
exts-agree f zero = refl
exts-agree f (suc x) = refl

act-id-on-μ-b-untyped : ∀ (f : Fin ℓ → Fin ℓ') b
                      → CR.act-ε f (μ-b-untyped b) ≡ μ-b-untyped b
act-id-on-μ-b-untyped f BUnit = refl

infixl 10 _then_
_then_ : ∀ {S : Set} {a b c : S}
       → a ≡ b
       → b ≡ c
       → a ≡ c
refl then refl = refl

mutual
  μ-ρ-weaken-commute : (f : Fin ℓ → Fin ℓ')
                     → (ρ : Refinement ℓ)
                     → μ-ρ-untyped (SR.act-ρ f ρ) ≡ CR.act-ε f (μ-ρ-untyped ρ)

  μ-τ-weaken-commute : (f : Fin ℓ → Fin ℓ')
                     → (τˢ : SType ℓ)
                     → μ-τ-untyped (SR.act-τ f τˢ) ≡ CR.act-ε f (μ-τ-untyped τˢ)
  μ-τ-weaken-commute f ⟨ b ∣ ε₁ ≈ ε₂ of τ ⟩ = {! !}
  μ-τ-weaken-commute f ⟨ b ∣ ρ₁ ∧ ρ₂ ⟩ = lemma₁
                                    then lemma₂
                                    then lemma₃
                                    then lemma₄
                                    then lemma₅
    where
    lemma₁ : μ-τ-untyped (SR.act-τ f ⟨ b ∣ ρ₁ ∧ ρ₂ ⟩)
             ≡
             Σ[ μ-b-untyped b ]
                 CLam (μ-b-untyped b)
                      ⟨ CR.act-ε (CR.ext f) (μ-ρ-untyped ρ₁)
                      × CR.act-ε (CR.ext f) (μ-ρ-untyped ρ₂)
                      ⟩
    lemma₁ rewrite μ-ρ-weaken-commute (SR.ext f) ρ₁
                 | μ-ρ-weaken-commute (SR.ext f) ρ₂
                 | CR.act-ε-extensionality (exts-agree f) (μ-ρ-untyped ρ₁)
                 | CR.act-ε-extensionality (exts-agree f) (μ-ρ-untyped ρ₂)
                 = refl

    lemma₂ : Σ[ μ-b-untyped b ]
                 CLam (μ-b-untyped b)
                      ⟨ CR.act-ε (CR.ext f) (μ-ρ-untyped ρ₁)
                      × CR.act-ε (CR.ext f) (μ-ρ-untyped ρ₂)
                      ⟩
             ≡
             Σ[ CR.act-ε f (μ-b-untyped b) ]
                 CLam (CR.act-ε f (μ-b-untyped b))
                      ⟨ CR.act-ε (CR.ext f) (μ-ρ-untyped ρ₁)
                      × CR.act-ε (CR.ext f) (μ-ρ-untyped ρ₂)
                      ⟩
    lemma₂ rewrite act-id-on-μ-b-untyped f b = refl

    lemma₃ : Σ[ CR.act-ε f (μ-b-untyped b) ]
                 CLam (CR.act-ε f (μ-b-untyped b))
                      ⟨ CR.act-ε (CR.ext f) (μ-ρ-untyped ρ₁)
                      × CR.act-ε (CR.ext f) (μ-ρ-untyped ρ₂)
                      ⟩
             ≡
             Σ[ CR.act-ε f (μ-b-untyped b) ]
                 CR.act-ε f (CLam (μ-b-untyped b)
                                  ⟨ μ-ρ-untyped ρ₁
                                  × μ-ρ-untyped ρ₂
                                  ⟩)
    lemma₃ = {! !}

    lemma₄ : Σ[ CR.act-ε f (μ-b-untyped b) ]
                 CR.act-ε f (CLam (μ-b-untyped b)
                                  ⟨ μ-ρ-untyped ρ₁
                                  × μ-ρ-untyped ρ₂
                                  ⟩)
             ≡
             CR.act-ε f (Σ[ μ-b-untyped b ]
                 CLam (μ-b-untyped b)
                      ⟨ μ-ρ-untyped ρ₁
                      × μ-ρ-untyped ρ₂
                      ⟩)
    lemma₄ rewrite act-Σ-commutes
                    f
                    (μ-b-untyped b)
                    (CLam (μ-b-untyped b) ⟨ μ-ρ-untyped ρ₁
                                          × μ-ρ-untyped ρ₂
                                          ⟩)
                 = refl

    lemma₅ : CR.act-ε f (Σ[ μ-b-untyped b ] CLam (μ-b-untyped b) ⟨ μ-ρ-untyped ρ₁
                                                                 × μ-ρ-untyped ρ₂
                                                                 ⟩)
             ≡
             CR.act-ε f (μ-τ-untyped ⟨ b ∣ ρ₁ ∧ ρ₂ ⟩)
    lemma₅ = refl
  μ-τ-weaken-commute f ⟨ BUnit ∣ Τ ⟩ = refl
  μ-τ-weaken-commute f (τˢ₁ ⇒ τˢ₂)
    rewrite μ-τ-weaken-commute f τˢ₁
          | μ-τ-weaken-commute (SR.ext f) τˢ₂
          | CR.act-ε-extensionality (exts-agree f) (μ-τ-untyped τˢ₂)
          = refl
  μ-τ-weaken-commute f (⊍ cons) = {! !}
