{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Safety.Helpers where

open import Data.Fin using (zero; suc)
open import Data.Nat using (zero)
open import Data.Vec.Base using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Derivations.Algorithmic
open import Surface.Operational

data Canonical : STerm ℓ → SType ℓ → Set where
  C-Lam  : Canonical (SLam τ ε) (τ₁ ⇒ τ₂)
  C-Con  : ∀ {cons cons' : ADTCons (Mkℕₐ (suc n)) zero}
         → Canonical (SCon ι ε cons) (⊍ cons')

canonical-⇒ : ⊘ ⊢[ θ , φ of κ ] ε ⦂ τ
            → IsValue ε
            → τ ≡ τ₁ ⇒ τ₂
            → Canonical ε τ
canonical-⇒ (T-Abs arrδ εδ) is-value ≡-prf = C-Lam
canonical-⇒ (T-Sub εδ τ'δ (ST-Arr _ _ _ _)) is-value refl
  with C-Lam ← canonical-⇒ εδ is-value refl = C-Lam

canonical-⊍ : {cons : ADTCons (Mkℕₐ n) zero}
            → ⊘ ⊢[ θ , φ of κ ] ε ⦂ τ
            → IsValue ε
            → τ ≡ ⊍ cons
            → Canonical ε τ
canonical-⊍ (T-Con ≡-prf₁ εδ adtτ) (IV-ADT is-value) ≡-prf = C-Con
canonical-⊍ (T-Sub εδ τ'δ ()) _ refl
