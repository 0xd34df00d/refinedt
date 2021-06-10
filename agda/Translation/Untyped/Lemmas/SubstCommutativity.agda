{-# OPTIONS --safe #-}

module Translation.Untyped.Lemmas.SubstCommutativity where

open import Data.Vec using (_∷_; [])
open import Data.Fin using (zero; suc)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Data.Fin.Extra

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
open import Translation.Untyped.Lemmas.Misc hiding (exts-agree)
import      Translation.Untyped.Lemmas.RenamingCommutativity as TURC

exts-agree : (f : Fin ℓ → STerm ℓ')
           → ⌊μ⌋-ε ∘ SS.ext f f≡ CS.ext (⌊μ⌋-ε ∘ f)
exts-agree f zero = refl
exts-agree f (suc ι) = TURC.⌊μ⌋-ε-act-commute suc (f ι)

act-id-on-⌊μ⌋-b : ∀ (f : Fin ℓ → CExpr ℓ') b
                      → CS.act-ε f (⌊μ⌋-b b) ≡ ⌊μ⌋-b b
act-id-on-⌊μ⌋-b _ BUnit = refl

mutual
  ⌊μ⌋-ρ-commute : (f : Fin ℓ → STerm ℓ')
              → (ρ : Refinement ℓ)
              → ⌊μ⌋-ρ (SS.act-ρ f ρ) ≡ CS.act-ε (⌊μ⌋-ε ∘ f) (⌊μ⌋-ρ ρ)
  ⌊μ⌋-ρ-commute f (ε₁ ≈ ε₂ of τ)
    rewrite CS.act-≡̂-commutes (⌊μ⌋-ε ∘ f) (⌊μ⌋-ε ε₁) (⌊μ⌋-ε ε₂) (⌊μ⌋-τ τ)
          | ⌊μ⌋-ε-commute f ε₁
          | ⌊μ⌋-ε-commute f ε₂
          | ⌊μ⌋-τ-commute f τ
          = refl
  ⌊μ⌋-ρ-commute f (ρ₁ ∧ ρ₂)
    rewrite act-×-commutes (⌊μ⌋-ε ∘ f) (⌊μ⌋-ρ ρ₁) (⌊μ⌋-ρ ρ₂)
          | ⌊μ⌋-ρ-commute f ρ₁
          | ⌊μ⌋-ρ-commute f ρ₂
          = refl
  ⌊μ⌋-ρ-commute f Τ = refl

  common-ρ-steps : ∀ (f : Fin ℓ → STerm ℓ') b ρ
                 → Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) (⌊μ⌋-ρ (SS.act-ρ (SS.ext f) ρ))
                   ≡
                   CS.act-ε (⌊μ⌋-ε ∘ f) (Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) (⌊μ⌋-ρ ρ))
  common-ρ-steps f b ρ = step₁ then step₂ then step₃
    where
    fᶜ = ⌊μ⌋-ε ∘ f

    step₁ : Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) (⌊μ⌋-ρ (SS.act-ρ (SS.ext f) ρ))
            ≡
            Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) (CS.act-ε (CS.ext fᶜ) (⌊μ⌋-ρ ρ))
    step₁ = cong
              (λ ε → Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) ε)
              (⌊μ⌋-ρ-commute (SS.ext f) ρ
          then CS.act-ε-extensionality (exts-agree f) (⌊μ⌋-ρ ρ))

    step₂ : Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) (CS.act-ε (CS.ext fᶜ) (⌊μ⌋-ρ ρ))
            ≡
            Σ[ CS.act-ε fᶜ (⌊μ⌋-b b) ] CLam (CS.act-ε fᶜ (⌊μ⌋-b b)) (CS.act-ε (CS.ext fᶜ) (⌊μ⌋-ρ ρ))
    step₂ rewrite act-id-on-⌊μ⌋-b fᶜ b = refl

    step₃ : Σ[ CS.act-ε fᶜ (⌊μ⌋-b b) ] CLam (CS.act-ε fᶜ (⌊μ⌋-b b)) (CS.act-ε (CS.ext fᶜ) (⌊μ⌋-ρ ρ))
            ≡
            CS.act-ε fᶜ (Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) (⌊μ⌋-ρ ρ))
    step₃ rewrite act-Σ-commutes fᶜ (⌊μ⌋-b b) (CLam (⌊μ⌋-b b) (⌊μ⌋-ρ ρ)) = refl

  ⌊μ⌋-τ-commute : (f : Fin ℓ → STerm ℓ')
              → (τˢ : SType ℓ)
              → ⌊μ⌋-τ (SS.act-τ f τˢ) ≡ CS.act-ε (⌊μ⌋-ε ∘ f) (⌊μ⌋-τ τˢ)
  ⌊μ⌋-τ-commute f ⟨ BUnit ∣ Τ ⟩ = refl
  ⌊μ⌋-τ-commute f ⟨ b ∣ ρ@(_ ≈ _ of _) ⟩ = common-ρ-steps f b ρ
  ⌊μ⌋-τ-commute f ⟨ b ∣ ρ@(_ ∧ _) ⟩ = common-ρ-steps f b ρ
  ⌊μ⌋-τ-commute f (τ₁ ⇒ τ₂)
    rewrite ⌊μ⌋-τ-commute f τ₁
          | ⌊μ⌋-τ-commute (SS.ext f) τ₂
          | CS.act-ε-extensionality (exts-agree f) (⌊μ⌋-τ τ₂)
          = refl
  ⌊μ⌋-τ-commute f (⊍ cons) rewrite ⌊μ⌋-cons-commute f cons = refl

  ⌊μ⌋-ε-commute : (f : Fin ℓ → STerm ℓ')
              → (εˢ : STerm ℓ)
              → ⌊μ⌋-ε (SS.act-ε f εˢ) ≡ CS.act-ε (⌊μ⌋-ε ∘ f) (⌊μ⌋-ε εˢ)
  ⌊μ⌋-ε-commute f SUnit = refl
  ⌊μ⌋-ε-commute f (SVar ι) = refl
  ⌊μ⌋-ε-commute f (SLam τ ε)
    rewrite ⌊μ⌋-τ-commute f τ
          | ⌊μ⌋-ε-commute (SS.ext f) ε
          | CS.act-ε-extensionality (exts-agree f) (⌊μ⌋-ε ε)
          = refl
  ⌊μ⌋-ε-commute f (SApp ε₁ ε₂)
    rewrite ⌊μ⌋-ε-commute f ε₁
          | ⌊μ⌋-ε-commute f ε₂
          = refl
  ⌊μ⌋-ε-commute f (SCase ε branches)
    rewrite ⌊μ⌋-ε-commute f ε
          | ⌊μ⌋-branches-commute f branches
          = refl
  ⌊μ⌋-ε-commute f (SCon ι ε cons)
    rewrite ⌊μ⌋-ε-commute f ε
          | ⌊μ⌋-cons-commute f cons
          = refl

  ⌊μ⌋-cons-commute : (f : Fin ℓ → STerm ℓ')
                 → (cons : S.ADTCons nₐ ℓ)
                 → ⌊μ⌋-cons (SS.act-cons f cons) ≡ CS.act-cons (⌊μ⌋-ε ∘ f) (⌊μ⌋-cons cons)
  ⌊μ⌋-cons-commute f [] = refl
  ⌊μ⌋-cons-commute f (τ ∷ cons)
    rewrite ⌊μ⌋-τ-commute f τ
          | ⌊μ⌋-cons-commute f cons
          = refl

  ⌊μ⌋-branches-commute : (f : Fin ℓ → STerm ℓ')
                     → (bs : S.CaseBranches nₐ ℓ)
                     → ⌊μ⌋-branches (SS.act-branches f bs) ≡ CS.act-branches (⌊μ⌋-ε ∘ f) (⌊μ⌋-branches bs)
  ⌊μ⌋-branches-commute f [] = refl
  ⌊μ⌋-branches-commute f (MkCaseBranch ε ∷ bs)
    rewrite ⌊μ⌋-branches-commute f bs
          = refl
  -- TODO once again address this once branches translation is fixed

replace-at-agree : ∀ ι (ε : STerm ℓ)
                 → CS.replace-at ι (⌊μ⌋-ε ε) f≡ ⌊μ⌋-ε ∘ SS.replace-at ι ε
replace-at-agree ι ε ι' with ι <>? ι'
... | less m<n = refl
... | equal m≡n = refl
... | greater m>n = refl

⌊μ⌋-τ-preserves-↦ : ∀ ι ε (τ : SType (suc ℓ))
                → ⌊μ⌋-τ ([ ι ↦τ ε ] τ) ≡ ([ ι ↦ ⌊μ⌋-ε ε ] ⌊μ⌋-τ τ)
⌊μ⌋-τ-preserves-↦ ι ε τ
  rewrite CS.act-ε-extensionality (replace-at-agree ι ε) (⌊μ⌋-τ τ)
        = ⌊μ⌋-τ-commute (SS.replace-at ι ε) τ

⌊μ⌋-ε-preserves-↦ : ∀ ι ε₀ (ε : STerm (suc ℓ))
                → ⌊μ⌋-ε ([ ι ↦ε ε₀ ] ε) ≡ ([ ι ↦ ⌊μ⌋-ε ε₀ ] ⌊μ⌋-ε ε)
⌊μ⌋-ε-preserves-↦ ι ε₀ ε
  rewrite CS.act-ε-extensionality (replace-at-agree ι ε₀) (⌊μ⌋-ε ε)
        = ⌊μ⌋-ε-commute (SS.replace-at ι ε₀) ε
