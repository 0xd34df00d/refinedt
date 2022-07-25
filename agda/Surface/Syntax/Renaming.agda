{-# OPTIONS --safe #-}

module Surface.Syntax.Renaming where

open import Data.Fin using (zero; suc; raise)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat using (_+_; zero; suc)
open import Data.Vec
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import Common.Helpers
open import Common.Types
open import Data.Fin.Extra
open import Surface.Syntax
open import Surface.Syntax.Actions (record { Target = Fin
                                           ; var-action = λ ι → SVar ι
                                           ; ext = ext-ρ
                                           }) public

weaken-τ : SType ℓ → SType (suc ℓ)
weaken-τ = act-τ suc

weaken-ε : STerm ℓ → STerm (suc ℓ)
weaken-ε = act-ε suc

weaken-ρ : Refinement ℓ → Refinement (suc ℓ)
weaken-ρ = act-ρ suc

weaken-τ-k : ∀ k → SType ℓ → SType (k + ℓ)
weaken-τ-k k = act-τ (raise k)

weaken-ε-k : ∀ k → STerm ℓ → STerm (k + ℓ)
weaken-ε-k k = act-ε (raise k)


branch-lookup-comm : (ρ : Fin ℓ → Fin ℓ')
                   → (ι : Fin n)
                   → (bs : CaseBranches (Mkℕₐ n) ℓ)
                   → act-ε (ext ρ) (CaseBranch.body (lookup bs ι)) ≡ CaseBranch.body (lookup (act-branches ρ bs) ι)
branch-lookup-comm ρ zero (_ ∷ _) = refl
branch-lookup-comm ρ (suc ι) (_ ∷ bs) = branch-lookup-comm ρ ι bs

cons-lookup-comm : (ρ : Fin ℓ → Fin ℓ')
                 → (ι : Fin n)
                 → (cons : ADTCons (Mkℕₐ n) ℓ)
                 → act-τ ρ (lookup cons ι) ≡ lookup (act-cons ρ cons) ι
cons-lookup-comm ρ zero (τ ∷ _) = refl
cons-lookup-comm ρ (suc ι) (_ ∷ cons) = cons-lookup-comm ρ ι cons

SVar-inj : SVar ι₁ ≡ SVar ι₂
         → ι₁ ≡ ι₂
SVar-inj refl = refl

open import Surface.Syntax.Actions.Lemmas var-action-record
                                          record { ≡-ext = λ where x-≡ zero → refl
                                                                   x-≡ (suc x) → cong suc (x-≡ x)
                                                 ; ext-id = λ where f-≡ zero → refl
                                                                    f-≡ (suc x) → cong (SVar ∘ suc) (SVar-inj (f-≡ x))
                                                 }
                                          public


-- A composition of renamings is a renaming by the composition
ActDistributivity : {Ty : ℕ → Set} → ActionOn Ty → Set
ActDistributivity {Ty} act = ∀ {ℓ₀ ℓ₁ ℓ₂}
                             → (r₁ : Fin ℓ₀ → Fin ℓ₁)
                             → (r₂ : Fin ℓ₁ → Fin ℓ₂)
                             → act r₂ ∘ act r₁ f≡ act (r₂ ∘ r₁)

mutual
  act-τ-distr : ActDistributivity act-τ
  act-τ-distr r₁ r₂ ⟨ b ∣ ρ ⟩
    rewrite act-ρ-distr (ext r₁) (ext r₂) ρ
          | act-ρ-extensionality (ext-distr r₁ r₂) ρ
          = refl
  act-τ-distr r₁ r₂ (τ₁ ⇒ τ₂)
    rewrite act-τ-distr r₁ r₂ τ₁
          | act-τ-distr (ext r₁) (ext r₂) τ₂
          | act-τ-extensionality (ext-distr r₁ r₂) τ₂
          = refl
  act-τ-distr r₁ r₂ (⊍ cons) rewrite act-cons-distr r₁ r₂ cons = refl

  act-ρ-distr : ActDistributivity act-ρ
  act-ρ-distr r₁ r₂ (ε₁ ≈ ε₂ of τ)
    rewrite act-ε-distr r₁ r₂ ε₁
          | act-ε-distr r₁ r₂ ε₂
          | act-τ-distr r₁ r₂ τ
          = refl
  act-ρ-distr r₁ r₂ (ρ₁ ∧ ρ₂)
    rewrite act-ρ-distr r₁ r₂ ρ₁
          | act-ρ-distr r₁ r₂ ρ₂
          = refl
  act-ρ-distr _ _ Τ = refl

  act-ε-distr : ActDistributivity act-ε
  act-ε-distr r₁ r₂ SUnit = refl
  act-ε-distr r₁ r₂ (SVar ι) = refl
  act-ε-distr r₁ r₂ (SLam τ ε)
    rewrite act-τ-distr r₁ r₂ τ
          | act-ε-distr (ext r₁) (ext r₂) ε
          | act-ε-extensionality (ext-distr r₁ r₂) ε
          = refl
  act-ε-distr r₁ r₂ (SApp ε₁ ε₂)
    rewrite act-ε-distr r₁ r₂ ε₁
          | act-ε-distr r₁ r₂ ε₂
          = refl
  act-ε-distr r₁ r₂ (SCase ε cons τ branches)
    rewrite act-ε-distr r₁ r₂ ε
          | act-cons-distr r₁ r₂ cons
          | act-τ-distr r₁ r₂ τ
          | act-branches-distr r₁ r₂ branches
          = refl
  act-ε-distr r₁ r₂ (SCon ι ε cons)
    rewrite act-ε-distr r₁ r₂ ε
          | act-cons-distr r₁ r₂ cons
          = refl

  act-cons-distr : ActDistributivity {ADTCons nₐ} act-cons
  act-cons-distr r₁ r₂ [] = refl
  act-cons-distr r₁ r₂ (τ ∷ τs)
    rewrite act-τ-distr r₁ r₂ τ
          | act-cons-distr r₁ r₂ τs
          = refl

  act-branches-distr : ActDistributivity {CaseBranches nₐ} act-branches
  act-branches-distr r₁ r₂ [] = refl
  act-branches-distr r₁ r₂ (MkCaseBranch body ∷ bs)
    rewrite act-ε-distr (ext r₁) (ext r₂) body
          | act-branches-distr r₁ r₂ bs
          | act-ε-extensionality (ext-distr r₁ r₂) body
          = refl


weaken-τ-comm : ∀ (ρ : Fin ℓ → Fin ℓ') (τ : SType ℓ)
              → act-τ (ext ρ) (weaken-τ τ) ≡ weaken-τ (act-τ ρ τ)
weaken-τ-comm ρ τ
  rewrite act-τ-distr suc (ext ρ) τ
        | act-τ-distr ρ suc τ
        = refl

weaken-ε-comm : ∀ (ρ : Fin ℓ → Fin ℓ') (ε : STerm ℓ)
              → act-ε (ext ρ) (weaken-ε ε) ≡ weaken-ε (act-ε ρ ε)
weaken-ε-comm ρ ε
  rewrite act-ε-distr suc (ext ρ) ε
        | act-ε-distr ρ suc ε
        = refl


weaken-τ-suc-k : ∀ k (τ : SType ℓ)
               → weaken-τ-k (suc k) τ ≡ weaken-τ (weaken-τ-k k τ)
weaken-τ-suc-k k τ = sym (act-τ-distr (raise k) suc τ)

weaken-ε-suc-k : ∀ k (ε : STerm ℓ)
               → weaken-ε-k (suc k) ε ≡ weaken-ε (weaken-ε-k k ε)
weaken-ε-suc-k k ε = sym (act-ε-distr (raise k) suc ε)
