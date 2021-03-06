{-# OPTIONS --safe #-}

module Translation.Untyped.Lemmas.RenamingCommutativity where

open import Data.Vec using (_∷_; [])
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Common.Helpers
open import Core.Syntax as C renaming (Γ to Γᶜ)
open import Core.Syntax.Derived as C
open import Core.Syntax.Derived.Renaming as CR
open import Core.Syntax.Membership as C renaming (_∈_at_ to _∈ᶜ_at_)
import      Core.Syntax.Renaming as CR
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; ε to εˢ)
open import Surface.Syntax.Membership as S renaming (_∈_at_ to _∈ˢ_at_)
import      Surface.Syntax.Renaming as SR

open import Translation.Untyped
open import Translation.Untyped.Lemmas.Misc

act-id-on-⌊μ⌋-b : ∀ (f : Fin ℓ → Fin ℓ') b
                → CR.act-ε f (⌊μ⌋-b b) ≡ ⌊μ⌋-b b
act-id-on-⌊μ⌋-b f BUnit = refl

mutual
  ⌊μ⌋-ρ-act-commute : (f : Fin ℓ → Fin ℓ')
                    → (ρ : Refinement ℓ)
                    → ⌊μ⌋-ρ (SR.act-ρ f ρ) ≡ CR.act-ε f (⌊μ⌋-ρ ρ)
  ⌊μ⌋-ρ-act-commute f Τ = refl
  ⌊μ⌋-ρ-act-commute f (ε₁ ≈ ε₂ of τ)
    rewrite act-≡̂-commutes f (⌊μ⌋-ε ε₁) (⌊μ⌋-ε ε₂) (⌊μ⌋-τ τ)
          | ⌊μ⌋-ε-act-commute f ε₁
          | ⌊μ⌋-ε-act-commute f ε₂
          | ⌊μ⌋-τ-act-commute f τ
          = refl
  ⌊μ⌋-ρ-act-commute f (ρ₁ ∧ ρ₂)
    rewrite act-×-commutes f (⌊μ⌋-ρ ρ₁) (⌊μ⌋-ρ ρ₂)
          | ⌊μ⌋-ρ-act-commute f ρ₁
          | ⌊μ⌋-ρ-act-commute f ρ₂
          = refl

  common-ρ-steps : ∀ (f : Fin ℓ → Fin ℓ') b ρ
                 → Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) (⌊μ⌋-ρ (SR.act-ρ (SR.ext f) ρ))
                   ≡
                   CR.act-ε f (Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) (⌊μ⌋-ρ ρ))
  common-ρ-steps f b ρ = step₁ then step₂ then step₃
    where
    step₁ : Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) (⌊μ⌋-ρ (SR.act-ρ (SR.ext f) ρ))
            ≡
            Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) (CR.act-ε (CR.ext f) (⌊μ⌋-ρ ρ))
    step₁ = cong        -- rewrite fails for some reason beyond my Agda understanding, so let's do `cong` instead
              (λ ε → Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) ε)
              (⌊μ⌋-ρ-act-commute (SR.ext f) ρ
          then CR.act-ε-extensionality (exts-agree f) (⌊μ⌋-ρ ρ))

    step₂ : Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) (CR.act-ε (CR.ext f) (⌊μ⌋-ρ ρ))
            ≡
            Σ[ CR.act-ε f (⌊μ⌋-b b) ] CLam (CR.act-ε f (⌊μ⌋-b b)) (CR.act-ε (CR.ext f) (⌊μ⌋-ρ ρ))
    step₂ rewrite act-id-on-⌊μ⌋-b f b = refl

    step₃ : Σ[ CR.act-ε f (⌊μ⌋-b b) ] CLam (CR.act-ε f (⌊μ⌋-b b)) (CR.act-ε (CR.ext f) (⌊μ⌋-ρ ρ))
            ≡
            CR.act-ε f (Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) (⌊μ⌋-ρ ρ))
    step₃ rewrite act-Σ-commutes f (⌊μ⌋-b b) (CLam (⌊μ⌋-b b) (⌊μ⌋-ρ ρ)) = refl

  ⌊μ⌋-τ-act-commute : (f : Fin ℓ → Fin ℓ')
                    → (τˢ : SType ℓ)
                    → ⌊μ⌋-τ (SR.act-τ f τˢ) ≡ CR.act-ε f (⌊μ⌋-τ τˢ)
  ⌊μ⌋-τ-act-commute f ⟨ BUnit ∣ Τ ⟩ = refl
  ⌊μ⌋-τ-act-commute f ⟨ b ∣ ρ@(_ ∧ _) ⟩ = common-ρ-steps f b ρ
  ⌊μ⌋-τ-act-commute f ⟨ b ∣ ρ@(_ ≈ _ of _) ⟩ = common-ρ-steps f b ρ
  ⌊μ⌋-τ-act-commute f (τˢ₁ ⇒ τˢ₂)
    rewrite ⌊μ⌋-τ-act-commute f τˢ₁
          | ⌊μ⌋-τ-act-commute (SR.ext f) τˢ₂
          | CR.act-ε-extensionality (exts-agree f) (⌊μ⌋-τ τˢ₂)
          = refl
  ⌊μ⌋-τ-act-commute f (⊍ cons) rewrite ⌊μ⌋-cons-act-commute f cons = refl

  ⌊μ⌋-ε-act-commute : (f : Fin ℓ → Fin ℓ')
                    → (εˢ : STerm ℓ)
                    → ⌊μ⌋-ε (SR.act-ε f εˢ) ≡ CR.act-ε f (⌊μ⌋-ε εˢ)
  ⌊μ⌋-ε-act-commute f SUnit = refl
  ⌊μ⌋-ε-act-commute f (SVar ι) = refl
  ⌊μ⌋-ε-act-commute f (SLam τ ε)
    rewrite ⌊μ⌋-τ-act-commute f τ
          | ⌊μ⌋-ε-act-commute (SR.ext f) ε
          | CR.act-ε-extensionality (exts-agree f) (⌊μ⌋-ε ε)
          = refl
  ⌊μ⌋-ε-act-commute f (SApp ε₁ ε₂)
    rewrite ⌊μ⌋-ε-act-commute f ε₁
          | ⌊μ⌋-ε-act-commute f ε₂
          = refl
  ⌊μ⌋-ε-act-commute f (SCase ε branches)
    rewrite ⌊μ⌋-ε-act-commute f ε
          | ⌊μ⌋-branches-act-commute f branches
          = refl
  ⌊μ⌋-ε-act-commute f (SCon ι ε cons)
    rewrite ⌊μ⌋-ε-act-commute f ε
          | ⌊μ⌋-cons-act-commute f cons
          = refl

  ⌊μ⌋-cons-act-commute : (f : Fin ℓ → Fin ℓ')
                       → (cons : S.ADTCons nₐ ℓ)
                       → ⌊μ⌋-cons (SR.act-cons f cons) ≡ CR.act-cons f (⌊μ⌋-cons cons)
  ⌊μ⌋-cons-act-commute f [] = refl
  ⌊μ⌋-cons-act-commute f (τ ∷ cons)
    rewrite ⌊μ⌋-τ-act-commute f τ
          | ⌊μ⌋-cons-act-commute f cons
          = refl

  ⌊μ⌋-branches-act-commute : (f : Fin ℓ → Fin ℓ')
                         → (bs : S.CaseBranches nₐ ℓ)
                         → ⌊μ⌋-branches (SR.act-branches f bs) ≡ CR.act-branches f (⌊μ⌋-branches bs)
  ⌊μ⌋-branches-act-commute f [] = refl
  ⌊μ⌋-branches-act-commute f (MkCaseBranch ε ∷ bs)
    rewrite ⌊μ⌋-branches-act-commute f bs
          = refl
  -- TODO this will break once we fix the translation of ε

⌊μ⌋-Γ-preserves-∈ : τˢ ∈ˢ Γˢ at ι
                → ⌊μ⌋-τ τˢ ∈ᶜ ⌊μ⌋-Γ Γˢ at ι
⌊μ⌋-Γ-preserves-∈ (∈-zero {τ = τ} refl) rewrite ⌊μ⌋-τ-act-commute suc τ = ∈-zero refl
⌊μ⌋-Γ-preserves-∈ (∈-suc {τ = τ} refl ∈) rewrite ⌊μ⌋-τ-act-commute suc τ = ∈-suc refl (⌊μ⌋-Γ-preserves-∈ ∈)
