{-# OPTIONS --safe #-}

module Surface.Syntax.Renaming.Injectivity where

open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat using (zero; suc)
open import Data.Vec using (Vec; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Helpers
open import Common.Types

open import Surface.Syntax
open import Surface.Syntax.Injectivity
open import Surface.Syntax.Renaming

ActInjectivity : {Ty : ℕ → Set} → ActionOn Ty → Set
ActInjectivity {Ty} act = ∀ {ℓ ℓ'} {f : Fin ℓ → Fin ℓ'}
                          → Injective f
                          → Injective (act f)

mutual
  act-τ-injectivity : ActInjectivity act-τ
  act-τ-injectivity f-inj {⟨ b₁ ∣ ρ₁ ⟩} {⟨ b₂ ∣ ρ₂ ⟩} ≡-prf
    rewrite ⟨∣⟩-inj₁ ≡-prf
          | act-ρ-injectivity (ext-inj f-inj) (⟨∣⟩-inj₂ ≡-prf)
          = refl
  act-τ-injectivity f-inj {x₁₁ ⇒ x₁₂} {x₂₁ ⇒ x₂₂} ≡-prf
    rewrite act-τ-injectivity f-inj (⇒-inj₁ ≡-prf)
          | act-τ-injectivity (ext-inj f-inj) (⇒-inj₂ ≡-prf)
          = refl
  act-τ-injectivity f-inj {⊍ cons₁} {⊍ cons₂} ≡-prf
    with refl ← ⊍-inj-len ≡-prf
    rewrite act-cons-injectivity f-inj (⊍-inj-cons ≡-prf)
          = refl

  act-ρ-injectivity : ActInjectivity act-ρ
  act-ρ-injectivity f-inj {ε₁₁ ≈ ε₁₂ of τ₁} {ε₂₁ ≈ ε₂₂ of τ₂} ≡-prf
    rewrite act-ε-injectivity f-inj {ε₁₁} {ε₂₁} (≈-inj₁ ≡-prf)
          | act-ε-injectivity f-inj {ε₁₂} {ε₂₂} (≈-inj₂ ≡-prf)
          | act-τ-injectivity f-inj {τ₁}  {τ₂}  (≈-inj₃ ≡-prf)
          = refl
  act-ρ-injectivity f-inj {ρ₁₁ ∧ ρ₁₂} {ρ₂₁ ∧ ρ₂₂} ≡-prf
    rewrite act-ρ-injectivity f-inj (∧-inj₁ ≡-prf)
          | act-ρ-injectivity f-inj (∧-inj₂ ≡-prf)
          = refl
  act-ρ-injectivity f-inj {Τ} {Τ} ≡-prf = refl

  act-ε-injectivity : ActInjectivity act-ε
  act-ε-injectivity f-inj {SUnit} {SUnit} ≡-prf = refl
  act-ε-injectivity f-inj {SVar ι₁} {SVar ι₂} ≡-prf rewrite f-inj (SVar-inj ≡-prf) = refl
  act-ε-injectivity f-inj {SLam τ₁ ε₁} {SLam τ₂ ε₂} ≡-prf
    rewrite act-τ-injectivity f-inj (SLam-inj₁ ≡-prf)
          | act-ε-injectivity (ext-inj f-inj) {ε₁} {ε₂} (SLam-inj₂ ≡-prf)
          = refl
  act-ε-injectivity f-inj {SApp ε₁₁ ε₁₂} {SApp ε₂₁ ε₂₂} ≡-prf
    rewrite act-ε-injectivity f-inj {ε₁₁} {ε₂₁} (SApp-inj₁ ≡-prf)
          | act-ε-injectivity f-inj {ε₁₂} {ε₂₂} (SApp-inj₂ ≡-prf)
          = refl
  act-ε-injectivity f-inj {SCase ε₁ cons₁ τ₁ branches₁} {SCase ε₂ cons₂ τ₂ branches₂} ≡-prf
    with refl ← SCase-inj-len ≡-prf
    rewrite act-ε-injectivity f-inj {ε₁} {ε₂} (SCase-inj₁ ≡-prf)
          | act-cons-injectivity f-inj (SCase-inj₂ ≡-prf)
          | act-τ-injectivity f-inj (SCase-inj₃ ≡-prf)
          | act-branches-injectivity f-inj (SCase-inj₄ ≡-prf)
          = refl
  act-ε-injectivity f-inj {SCon idx ε₁ cons₁} {SCon idx₁ ε₂ cons₂} ≡-prf
    with refl ← SCon-inj-len ≡-prf
    rewrite SCon-inj₁ ≡-prf
          | act-ε-injectivity f-inj {ε₁} {ε₂} (SCon-inj₂ ≡-prf)
          | act-cons-injectivity f-inj (SCon-inj₃ ≡-prf)
          = refl

  act-cons-injectivity : ActInjectivity {ADTCons nₐ} act-cons
  act-cons-injectivity f-inj {[]} {[]} ≡-prf = refl
  act-cons-injectivity f-inj {τ₁ ∷ cons₁} {τ₂ ∷ cons₂} ≡-prf
    rewrite act-τ-injectivity f-inj (∷-inj₁ ≡-prf)
          | act-cons-injectivity f-inj (∷-inj₂ ≡-prf)
          = refl

  act-branches-injectivity : ActInjectivity {CaseBranches nₐ} act-branches
  act-branches-injectivity f-inj {[]} {[]} ≡-prf = refl
  act-branches-injectivity f-inj {MkCaseBranch ε₁ ∷ bs₁} {MkCaseBranch ε₂ ∷ bs₂} ≡-prf
    rewrite act-ε-injectivity (ext-inj f-inj) {ε₁} {ε₂} (CaseBranch-inj (∷-inj₁ ≡-prf))
          | act-branches-injectivity f-inj (∷-inj₂ ≡-prf)
          = refl

weaken-τ-injective : Injective {SType ℓ} {SType (suc ℓ)} weaken-τ
weaken-τ-injective = act-τ-injectivity suc-injective

weaken-ε-injective : Injective {STerm ℓ} {STerm (suc ℓ)} weaken-ε
weaken-ε-injective = act-ε-injectivity suc-injective
