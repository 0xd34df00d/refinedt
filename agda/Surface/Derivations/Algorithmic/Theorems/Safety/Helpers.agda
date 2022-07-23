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
canonical-⇒ (T-Abs εδ) is-value ≡-prf = C-Lam
canonical-⇒ (T-Sub εδ τ'δ (ST-Arr _ _)) is-value refl
  with C-Lam ← canonical-⇒ εδ is-value refl = C-Lam

canonical-⊍ : {cons : ADTCons (Mkℕₐ n) zero}
            → ⊘ ⊢[ θ , φ of κ ] ε ⦂ τ
            → IsValue ε
            → τ ≡ ⊍ cons
            → Canonical ε τ
canonical-⊍ (T-Con ≡-prf₁ εδ adtτ) (IV-ADT is-value) ≡-prf = C-Con
canonical-⊍ (T-Sub εδ τ'δ ST-ADT) (IV-ADT iv) refl
  with T-Con ≡-prf r adtτ ← εδ = C-Con


SLam-inv : Γ ⊢[ θ , φ of not-t-sub ] SLam τ ε ⦂ τ₁ ⇒ τ₂
         → Γ , τ₁ ⊢[ θ , φ of not-t-sub ] ε ⦂ τ₂
SLam-inv (T-Abs εδ) = εδ

lookup-preserves-Γ⊢τ : {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
                     → (ι : Fin (suc n))
                     → Γ ⊢[ θ , φ  ] ⊍ cons
                     → Γ ⊢[ θ , φ ] lookup cons ι
lookup-preserves-Γ⊢τ {φ = φ} ι (TWF-ADT consδs) = go ι consδs
  where
  go : (ι : Fin n)
     → {cons : ADTCons (Mkℕₐ n) ℓ}
     → All (Γ ⊢[ θ , φ ]_) cons
     → Γ ⊢[ θ , φ ] lookup cons ι
  go zero (τδ ∷ _) = τδ
  go (suc ι) (_ ∷ consδs) = go ι consδs

con-has-type : ∀ {cons cons' : ADTCons (Mkℕₐ (suc n)) ℓ} {ι}
             → Γ ⊢[ θ , φ of not-t-sub ] SCon ι ε cons ⦂ ⊍ cons'
             → Γ ⊢[ θ , φ of not-t-sub ] ε ⦂ lookup cons' ι
con-has-type (T-Con refl conδ adtτ) = conδ

subst-Γ⊢ε⦂τ-τ : τ₁ ≡ τ₂
              → Γ ⊢[ θ , φ of κ ] ε ⦂ τ₁
              → Γ ⊢[ θ , φ of κ ] ε ⦂ τ₂
subst-Γ⊢ε⦂τ-τ refl εδ = εδ
