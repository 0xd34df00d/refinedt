-- {-# OPTIONS --safe #-}

module Translation.Untyped.Lemmas where

open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

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
  μ-ρ-weaken-commute f Τ = refl
  μ-ρ-weaken-commute f (ε₁ ≈ ε₂ of τ)
    rewrite act-≡̂-commutes f (μ-ε-untyped ε₁) (μ-ε-untyped ε₂) (μ-τ-untyped τ)
          | μ-ε-weaken-commute f ε₁
          | μ-ε-weaken-commute f ε₂
          | μ-τ-weaken-commute f τ
          = refl
  μ-ρ-weaken-commute f (ρ₁ ∧ ρ₂)
    rewrite act-×-commutes f (μ-ρ-untyped ρ₁) (μ-ρ-untyped ρ₂)
          | μ-ρ-weaken-commute f ρ₁
          | μ-ρ-weaken-commute f ρ₂
          = refl

  common-ρ-steps : ∀ (f : Fin ℓ → Fin ℓ') b ρ
                 → Σ[ μ-b-untyped b ] CLam (μ-b-untyped b) (μ-ρ-untyped (SR.act-ρ (SR.ext f) ρ))
                   ≡
                   CR.act-ε f (Σ[ μ-b-untyped b ] CLam (μ-b-untyped b) (μ-ρ-untyped ρ))
  common-ρ-steps f b ρ = step₁ then step₂ then step₃
    where
    step₁ : Σ[ μ-b-untyped b ] CLam (μ-b-untyped b) (μ-ρ-untyped (SR.act-ρ (SR.ext f) ρ))
            ≡
            Σ[ μ-b-untyped b ] CLam (μ-b-untyped b) (CR.act-ε (CR.ext f) (μ-ρ-untyped ρ))
    step₁ = cong        -- rewrite fails for some reason beyond my Agda understanding, so let's do `cong` instead
              (λ ε → Σ[ μ-b-untyped b ] CLam (μ-b-untyped b) ε)
              (μ-ρ-weaken-commute (SR.ext f) ρ
          then CR.act-ε-extensionality (exts-agree f) (μ-ρ-untyped ρ))

    step₂ : Σ[ μ-b-untyped b ] CLam (μ-b-untyped b) (CR.act-ε (CR.ext f) (μ-ρ-untyped ρ))
            ≡
            Σ[ CR.act-ε f (μ-b-untyped b) ] CLam (CR.act-ε f (μ-b-untyped b)) (CR.act-ε (CR.ext f) (μ-ρ-untyped ρ))
    step₂ rewrite act-id-on-μ-b-untyped f b = refl

    step₃ : Σ[ CR.act-ε f (μ-b-untyped b) ] CLam (CR.act-ε f (μ-b-untyped b)) (CR.act-ε (CR.ext f) (μ-ρ-untyped ρ))
            ≡
            CR.act-ε f (Σ[ μ-b-untyped b ] CLam (μ-b-untyped b) (μ-ρ-untyped ρ))
    step₃ rewrite act-Σ-commutes f (μ-b-untyped b) (CLam (μ-b-untyped b) (μ-ρ-untyped ρ)) = refl

  μ-τ-weaken-commute : (f : Fin ℓ → Fin ℓ')
                     → (τˢ : SType ℓ)
                     → μ-τ-untyped (SR.act-τ f τˢ) ≡ CR.act-ε f (μ-τ-untyped τˢ)
  μ-τ-weaken-commute f ⟨ BUnit ∣ Τ ⟩ = refl
  μ-τ-weaken-commute f ⟨ b ∣ ρ@(_ ∧ _) ⟩ = common-ρ-steps f b ρ
  μ-τ-weaken-commute f ⟨ b ∣ ρ@(_ ≈ _ of _) ⟩ = common-ρ-steps f b ρ
  μ-τ-weaken-commute f (τˢ₁ ⇒ τˢ₂)
    rewrite μ-τ-weaken-commute f τˢ₁
          | μ-τ-weaken-commute (SR.ext f) τˢ₂
          | CR.act-ε-extensionality (exts-agree f) (μ-τ-untyped τˢ₂)
          = refl
  μ-τ-weaken-commute f (⊍ cons) = {! !}

  μ-ε-weaken-commute : (f : Fin ℓ → Fin ℓ')
                     → (εˢ : STerm ℓ)
                     → μ-ε-untyped (SR.act-ε f εˢ) ≡ CR.act-ε f (μ-ε-untyped εˢ)
  μ-ε-weaken-commute f SUnit = refl
  μ-ε-weaken-commute f (SVar ι) = refl
  μ-ε-weaken-commute f (SLam τ ε)
    rewrite μ-τ-weaken-commute f τ
          | μ-ε-weaken-commute (SR.ext f) ε
          | CR.act-ε-extensionality (exts-agree f) (μ-ε-untyped ε)
          = refl
  μ-ε-weaken-commute f (SApp ε₁ ε₂)
    rewrite μ-ε-weaken-commute f ε₁
          | μ-ε-weaken-commute f ε₂
          = refl
  μ-ε-weaken-commute f (SCase ε branches) = {! !}
  μ-ε-weaken-commute f (SCon ι ε adt-cons) = {! !}
