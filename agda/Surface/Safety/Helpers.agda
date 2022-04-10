{-# OPTIONS --safe #-}

module Surface.Safety.Helpers where

open import Data.Fin using (zero; suc)
open import Data.Nat using (zero)
open import Data.Vec.Base using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Derivations
open import Surface.Operational
open import Surface.Theorems.Subtyping

data Canonical : STerm ℓ → SType ℓ → Set where
  C-Lam  : Canonical (SLam τ ε) (τ₁ ⇒ τ₂)
  C-Con  : ∀ {cons cons' : ADTCons (Mkℕₐ (suc n)) zero}
         → Canonical (SCon ι ε cons) (⊍ cons')

canonical-⇒ : ⊘ ⊢[ φ ] ε ⦂ τ
            → IsValue ε
            → τ ≡ τ₁ ⇒ τ₂
            → Canonical ε τ
canonical-⇒ (T-Abs arrδ εδ) is-value ≡-prf = C-Lam
canonical-⇒ (T-Sub εδ τ'δ <:@(ST-Arr _ _ _ _)) is-value refl with canonical-⇒ εδ is-value refl
... | C-Lam = C-Lam

canonical-⊍ : {cons : ADTCons (Mkℕₐ n) zero}
            → ⊘ ⊢[ φ ] ε ⦂ τ
            → IsValue ε
            → τ ≡ ⊍ cons
            → Canonical ε τ
canonical-⊍ (T-Con ≡-prf₁ εδ adtτ) (IV-ADT is-value) ≡-prf = C-Con
canonical-⊍ (T-Sub εδ τ'δ ()) _ refl


SLam-inv : Γ ⊢[ φ ] SLam τ ε ⦂ τ₁ ⇒ τ₂
         → Γ , τ₁ ⊢[ φ ] ε ⦂ τ₂
SLam-inv (T-Abs _ εδ) = εδ
SLam-inv (T-Sub εδ (TWF-Arr τ₁-ok τ₂-ok₁) (ST-Arr <:₁ <:₂ _ _)) = T-Sub (Γ⊢ε⦂τ-narrowing ⊘ <:₁ τ₁-ok (SLam-inv εδ)) τ₂-ok₁ <:₂


lookup-preserves-Γ⊢τ : {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
                     → (ι : Fin (suc n))
                     → Γ ⊢[ φ ] ⊍ cons
                     → Γ ⊢[ φ ] lookup cons ι
lookup-preserves-Γ⊢τ {φ = φ} ι (TWF-ADT consδs) = go ι consδs
  where
  go : (ι : Fin n)
     → {cons : ADTCons (Mkℕₐ n) ℓ}
     → All (Γ ⊢[ φ ]_) cons
     → Γ ⊢[ φ ] lookup cons ι
  go zero (px ∷ _) = px
  go (suc ι) (_ ∷ consδs) = go ι consδs

con-has-type : ∀ {cons cons' : ADTCons (Mkℕₐ (suc n)) ℓ} {ι}
             → Γ ⊢[ φ ] SCon ι ε cons ⦂ ⊍ cons'
             → Γ ⊢[ φ ] ε ⦂ lookup cons' ι
con-has-type (T-Con refl conδ adtτ) = conδ

subst-Γ⊢ε⦂τ-τ : τ₁ ≡ τ₂
              → Γ ⊢[ φ ] ε ⦂ τ₁
              → Γ ⊢[ φ ] ε ⦂ τ₂
subst-Γ⊢ε⦂τ-τ refl εδ = εδ
