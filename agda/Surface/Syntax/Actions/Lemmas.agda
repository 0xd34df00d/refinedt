{-# OPTIONS --safe #-}

open import Surface.Syntax

module Surface.Syntax.Actions.Lemmas (act : VarAction) (props : VarActionProps act) where

open import Data.Fin using (zero; suc)
open import Data.Vec
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax.Actions act
open VarActionProps props

ActExtensionality : {Ty : ℕ → Set} → ActionOn Ty → Set
ActExtensionality {Ty} act = ∀ {ℓ ℓ'}
                             → {f₁ f₂ : Fin ℓ → Target ℓ'}
                             → ((x : Fin ℓ) → f₁ x ≡ f₂ x)
                             → (v : Ty ℓ)
                             → act f₁ v ≡ act f₂ v

mutual
  act-τ-extensionality : ActExtensionality act-τ
  act-τ-extensionality x-≡ ⟨ b ∣ ρ ⟩ rewrite act-ρ-extensionality (≡-ext x-≡) ρ = refl
  act-τ-extensionality x-≡ (τ₁ ⇒ τ₂)
    rewrite act-τ-extensionality x-≡ τ₁
          | act-τ-extensionality (≡-ext x-≡) τ₂
          = refl
  act-τ-extensionality x-≡ (⊍ cons) rewrite act-cons-extensionality x-≡ cons = refl

  act-ρ-extensionality : ActExtensionality act-ρ
  act-ρ-extensionality x-≡ (ε₁ ≈ ε₂ of τ)
    rewrite act-ε-extensionality x-≡ ε₁
          | act-ε-extensionality x-≡ ε₂
          | act-τ-extensionality x-≡ τ
          = refl
  act-ρ-extensionality x-≡ (ρ₁ ∧ ρ₂)
    rewrite act-ρ-extensionality x-≡ ρ₁
          | act-ρ-extensionality x-≡ ρ₂
          = refl
  act-ρ-extensionality _ Τ = refl

  act-ε-extensionality : ActExtensionality act-ε
  act-ε-extensionality x-≡ SUnit = refl
  act-ε-extensionality x-≡ (SVar ι) rewrite x-≡ ι = refl
  act-ε-extensionality x-≡ (SLam τ ε)
    rewrite act-τ-extensionality x-≡ τ
          | act-ε-extensionality (≡-ext x-≡) ε
          = refl
  act-ε-extensionality x-≡ (SApp ε₁ ε₂)
    rewrite act-ε-extensionality x-≡ ε₁
          | act-ε-extensionality x-≡ ε₂
          = refl
  act-ε-extensionality x-≡ (SCase ε cons τ branches)
    rewrite act-ε-extensionality x-≡ ε
          | act-cons-extensionality x-≡ cons
          | act-τ-extensionality x-≡ τ
          | act-branches-extensionality x-≡ branches
          = refl
  act-ε-extensionality x-≡ (SCon ι ε cons)
    rewrite act-ε-extensionality x-≡ ε
          | act-cons-extensionality x-≡ cons
          = refl

  act-cons-extensionality : ActExtensionality {ADTCons nₐ} act-cons
  act-cons-extensionality x-≡ [] = refl
  act-cons-extensionality x-≡ (τ ∷ τs)
    rewrite act-τ-extensionality x-≡ τ
          | act-cons-extensionality x-≡ τs
          = refl

  act-branches-extensionality : ActExtensionality {CaseBranches nₐ} act-branches
  act-branches-extensionality x-≡ [] = refl
  act-branches-extensionality x-≡ (MkCaseBranch body ∷ bs)
    rewrite act-ε-extensionality (≡-ext x-≡) body
          | act-branches-extensionality x-≡ bs
          = refl

act-cons-member : ∀ {act : Fin ℓ → Target ℓ'}
                → (ι : _)
                → (cons : ADTCons (Mkℕₐ n) ℓ)
                → τ ≡ lookup cons ι
                → act-τ act τ ≡ lookup (act-cons act cons) ι
act-cons-member zero (conτ ∷ cons) refl = refl
act-cons-member (suc ι) (conτ ∷ cons) ≡-prf = act-cons-member ι cons ≡-prf


ActIdentity : {Ty : ℕ → Set} → ActionOn Ty → Set
ActIdentity {Ty} act = ∀ {ℓ} {f : Fin ℓ → Target ℓ}
                       → (∀ x → var-action (f x) ≡ SVar x)
                       → (v : Ty ℓ)
                       → act f v ≡ v

mutual
  act-τ-id : ActIdentity act-τ
  act-τ-id f-id ⟨ b ∣ ρ ⟩ rewrite act-ρ-id (ext-id f-id) ρ = refl
  act-τ-id f-id (τ₁ ⇒ τ₂)
    rewrite act-τ-id f-id τ₁
          | act-τ-id (ext-id f-id) τ₂
          = refl
  act-τ-id f-id (⊍ cons) rewrite act-cons-id f-id cons = refl

  act-ρ-id : ActIdentity act-ρ
  act-ρ-id f-id (ε₁ ≈ ε₂ of τ)
    rewrite act-ε-id f-id ε₁
          | act-ε-id f-id ε₂
          | act-τ-id f-id τ
          = refl
  act-ρ-id f-id (ρ₁ ∧ ρ₂)
    rewrite act-ρ-id f-id ρ₁
          | act-ρ-id f-id ρ₂
          = refl
  act-ρ-id _ Τ = refl

  act-ε-id : ActIdentity act-ε
  act-ε-id f-id SUnit = refl
  act-ε-id f-id (SVar ι) rewrite f-id ι = refl
  act-ε-id f-id (SLam τ ε)
    rewrite act-τ-id f-id τ
          | act-ε-id (ext-id f-id) ε
          = refl
  act-ε-id f-id (SApp ε₁ ε₂)
    rewrite act-ε-id f-id ε₁
          | act-ε-id f-id ε₂
          = refl
  act-ε-id f-id (SCase ε cons τ branches)
    rewrite act-ε-id f-id ε
          | act-cons-id f-id cons
          | act-τ-id f-id τ
          | act-branches-id f-id branches
          = refl
  act-ε-id f-id (SCon ι ε cons)
    rewrite act-ε-id f-id ε
          | act-cons-id f-id cons
          = refl

  act-cons-id : ActIdentity {ADTCons nₐ} act-cons
  act-cons-id f-id [] = refl
  act-cons-id f-id (τ ∷ cons)
    rewrite act-τ-id f-id τ
          | act-cons-id f-id cons
          = refl

  act-branches-id : ActIdentity {CaseBranches nₐ} act-branches
  act-branches-id f-id [] = refl
  act-branches-id f-id (MkCaseBranch body ∷ bs)
    rewrite act-ε-id (ext-id f-id) body
          | act-branches-id f-id bs
          = refl
