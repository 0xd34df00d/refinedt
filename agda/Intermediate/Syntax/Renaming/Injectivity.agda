{-# OPTIONS --safe #-}

module Intermediate.Syntax.Renaming.Injectivity where

open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat using (zero; suc)
open import Data.Vec using (Vec; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Helpers
open import Common.Types

open import Intermediate.Syntax
open import Intermediate.Syntax.Injectivity
open import Intermediate.Syntax.Renaming

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
  act-τ-injectivity f-inj {⊍ cons₁} {⊍ cons₂} ≡-prf with ⊍-inj-len ≡-prf
  ... | refl rewrite act-cons-injectivity f-inj (⊍-inj-cons ≡-prf) = refl

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
  act-ε-injectivity f-inj {IUnit} {IUnit} ≡-prf = refl
  act-ε-injectivity f-inj {IVar ι₁} {IVar ι₂} ≡-prf rewrite f-inj (IVar-inj ≡-prf) = refl
  act-ε-injectivity f-inj {ILam τ₁ ε₁} {ILam τ₂ ε₂} ≡-prf
    rewrite act-τ-injectivity f-inj (ILam-inj₁ ≡-prf)
          | act-ε-injectivity (ext-inj f-inj) {ε₁} {ε₂} (ILam-inj₂ ≡-prf)
          = refl
  act-ε-injectivity f-inj {IApp ε₁₁ ε₁₂} {IApp ε₂₁ ε₂₂} ≡-prf
    rewrite act-ε-injectivity f-inj {ε₁₁} {ε₂₁} (IApp-inj₁ ≡-prf)
          | act-ε-injectivity f-inj {ε₁₂} {ε₂₂} (IApp-inj₂ ≡-prf)
          = refl
  act-ε-injectivity f-inj {ICase ε₁ branches₁} {ICase ε₂ branches₂} ≡-prf with ICase-inj-len ≡-prf
  ... | refl
        rewrite act-ε-injectivity f-inj {ε₁} {ε₂} (ICase-inj₁ ≡-prf)
              | act-branches-injectivity f-inj (ICase-inj₂ ≡-prf)
              = refl
  act-ε-injectivity f-inj {ICon idx ε₁ cons₁} {ICon idx₁ ε₂ cons₂} ≡-prf with ICon-inj-len ≡-prf
  ... | refl
        rewrite ICon-inj₁ ≡-prf
              | act-ε-injectivity f-inj {ε₁} {ε₂} (ICon-inj₂ ≡-prf)
              | act-cons-injectivity f-inj (ICon-inj₃ ≡-prf)
              = refl
  act-ε-injectivity f-inj {ε₁ I<: τ₁} {ε₂ I<: τ₂} ≡-prf
    rewrite act-ε-injectivity f-inj {ε₁} {ε₂} (I<:-inj₁ ≡-prf)
          | act-τ-injectivity f-inj (I<:-inj₂ ≡-prf)
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

weaken-τ-injective : Injective {IType ℓ} {IType (suc ℓ)} weaken-τ
weaken-τ-injective = act-τ-injectivity suc-injective

weaken-ε-injective : Injective {ITerm ℓ} {ITerm (suc ℓ)} weaken-ε
weaken-ε-injective = act-ε-injectivity suc-injective
