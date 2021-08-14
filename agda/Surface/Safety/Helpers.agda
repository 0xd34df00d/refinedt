{-# OPTIONS --safe #-}

module Surface.Safety.Helpers where

open import Data.Fin using (zero; suc)
open import Data.Nat using (zero)
open import Data.Vec.Base using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Shape
open import Surface.Derivations
open import Surface.Operational
open import Surface.Operational.BetaEquivalence
open import Surface.Theorems.Subtyping
open import Surface.Theorems.Γ-Equivalence

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
canonical-⇒ (T-RConv {τ = τ₁' ⇒ τ₂'} εδ τ'δ τ~τ') is-value refl with canonical-⇒ εδ is-value refl
... | C-Lam = C-Lam
canonical-⇒ (T-RConv {τ = ⟨ _ ∣ _ ⟩} εδ τ'δ τ~τ') is-value refl = shape-⊥-elim ↭βτ-preserves-shape τ~τ' (λ ())
canonical-⇒ (T-RConv {τ = ⊍ _} εδ τ'δ τ~τ')       is-value refl = shape-⊥-elim ↭βτ-preserves-shape τ~τ' (λ ())

canonical-⊍ : {cons : ADTCons (Mkℕₐ n) zero}
            → ⊘ ⊢[ φ ] ε ⦂ τ
            → IsValue ε
            → τ ≡ ⊍ cons
            → Canonical ε τ
canonical-⊍ (T-Con ≡-prf₁ εδ adtτ) (IV-ADT is-value) ≡-prf = C-Con
canonical-⊍ (T-Sub εδ τ'δ ()) _ refl
canonical-⊍ (T-RConv {τ = ⊍ cons} εδ τ'δ τ~τ') is-value refl with canonical-⊍ εδ is-value refl | ↭βτ-cons-same-length τ~τ'
... | C-Con | refl = C-Con
canonical-⊍ (T-RConv {τ = ⟨ _ ∣ _ ⟩} εδ τ'δ τ~τ') is-value refl = shape-⊥-elim ↭βτ-preserves-shape τ~τ' (λ ())
canonical-⊍ (T-RConv {τ = _ ⇒ _} εδ τ'δ τ~τ')     is-value refl = shape-⊥-elim ↭βτ-preserves-shape τ~τ' (λ ())


SLam-inv : Γ ⊢[ φ ] SLam τ ε ⦂ τ₁ ⇒ τ₂
         → Γ , τ₁ ⊢[ φ ] ε ⦂ τ₂
SLam-inv (T-Abs _ εδ) = εδ
SLam-inv (T-Sub εδ (TWF-Arr τ₁-ok τ₂-ok₁) (ST-Arr <:₁ <:₂ _ _)) = T-Sub (Γ⊢ε⦂τ-narrowing ⊘ <:₁ τ₁-ok (SLam-inv εδ)) τ₂-ok₁ <:₂
SLam-inv (T-RConv {τ = τ₁' ⇒ τ₂'} εδ (TWF-Arr τ₁δ τ₂δ) τ~τ')
  = let Γ,τ₁⊢ε⦂τ₂' = Γ⊢ε⦂τ-equivalence ⊘ (↭βτ-⇒-dom τ~τ') τ₁δ (SLam-inv εδ)
     in T-RConv Γ,τ₁⊢ε⦂τ₂' τ₂δ (↭βτ-⇒-cod τ~τ')
SLam-inv (T-RConv {τ = ⟨ _ ∣ _ ⟩} εδ _ τ↝τ') = shape-⊥-elim ↭βτ-preserves-shape τ↝τ' λ ()
SLam-inv (T-RConv {τ = ⊍ _}       εδ _ τ↝τ') = shape-⊥-elim ↭βτ-preserves-shape τ↝τ' λ ()


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
con-has-type (T-RConv {τ = ⟨ _ ∣ _ ⟩} εδ _ τ↝τ') = shape-⊥-elim ↭βτ-preserves-shape τ↝τ' λ ()
con-has-type (T-RConv {τ = _ ⇒ _}     εδ _ τ↝τ') = shape-⊥-elim ↭βτ-preserves-shape τ↝τ' λ ()
con-has-type (T-RConv {τ = ⊍ cons}    εδ τ'δ τ↝τ') with ↭βτ-cons-same-length τ↝τ'
... | refl = T-RConv (con-has-type εδ) (lookup-preserves-Γ⊢τ _ τ'δ) (↭βτ-lookup _ τ↝τ')

subst-Γ⊢ε⦂τ-τ : τ₁ ≡ τ₂
              → Γ ⊢[ φ ] ε ⦂ τ₁
              → Γ ⊢[ φ ] ε ⦂ τ₂
subst-Γ⊢ε⦂τ-τ refl εδ = εδ
