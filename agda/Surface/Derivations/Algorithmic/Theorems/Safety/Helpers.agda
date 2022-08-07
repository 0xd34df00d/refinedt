{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Safety.Helpers where

open import Data.Fin using (zero; suc)
open import Data.Nat using (zero)
open import Data.Vec.Base using (lookup; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Subtyping
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
canonical-⇒ (T-Sub εδ (ST-Arr _ _)) is-value refl
  with C-Lam ← canonical-⇒ εδ is-value refl = C-Lam

canonical-⊍ : {cons : ADTCons (Mkℕₐ n) zero}
            → ⊘ ⊢[ θ , φ of κ ] ε ⦂ τ
            → IsValue ε
            → τ ≡ ⊍ cons
            → Canonical ε τ
canonical-⊍ (T-Con ≡-prf₁ εδ adtτ) (IV-ADT is-value) ≡-prf = C-Con
canonical-⊍ (T-Sub εδ (ST-ADT _)) (IV-ADT iv) refl
  with T-Con ≡-prf r adtτ ← εδ = C-Con


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

cons-lookup-<: : {cons' cons : ADTCons nₐ ℓ}
               → ∀ ι
               → AllSubtypes Γ θ φ cons' cons
               → Γ ⊢[ θ , φ ] lookup cons' ι <: lookup cons ι
cons-lookup-<: {cons' = _ ∷ _} {cons = _ ∷ _} zero    (<:δ ∷ _) = <:δ
cons-lookup-<: {cons' = _ ∷ _} {cons = _ ∷ _} (suc ι) (_ ∷ alls) = cons-lookup-<: ι alls

con-has-type : {cons' cons : ADTCons nₐ ℓ}
             → Γ ⊢[ θ , M of t-sub ] SCon ι ε cons' ⦂ ⊍ cons
             → Γ ⊢[ θ , M of t-sub ] ε ⦂ lookup cons ι
con-has-type (T-Sub (T-Con τⱼ-<:δ εδ _) (ST-ADT cons-<:))
  = T-Sub εδ (<:-transitive τⱼ-<:δ (cons-lookup-<: _ cons-<:))
