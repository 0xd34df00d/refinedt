{-# OPTIONS --safe #-}

module Surface.WellScoped.FreeVars where

open import Data.Fin public using (Fin; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (_∷_)

open import Surface.WellScoped

data _free-in-τ_ (ι : Fin ℓ) : (τ : SType ℓ) → Set
data _free-in-ρ_ (ι : Fin ℓ) : (τ : Refinement ℓ) → Set
data _free-in-ε_ (ι : Fin ℓ) : (ε : STerm ℓ) → Set
data _free-in-cons_ (ι : Fin ℓ) : (cons : ADTCons nₐ ℓ) → Set
data _free-in-branches_ (ι : Fin ℓ) : (cons : CaseBranches nₐ ℓ) → Set

data _free-in-τ_ {ℓ} ι where
  free-⟨∣⟩ : ∀ {ρ}
           → suc ι free-in-ρ ρ
           → ι free-in-τ ⟨ b ∣ ρ ⟩
  free-⇒   : ι free-in-τ τ₁ ⊎ suc ι free-in-τ τ₂
           → ι free-in-τ (τ₁ ⇒ τ₂)
  free-⊍   : ∀ {cons : ADTCons (Mkℕₐ (suc n)) ℓ}
           → ι free-in-cons cons
           → ι free-in-τ (⊍ cons)

data _free-in-ρ_ ι where
  free-≈ : ι free-in-ε ε₁ ⊎ ι free-in-ε ε₂
         → ι free-in-ρ (ε₁ ≈ ε₂)
  free-∧ : ι free-in-ρ ρ₁ ⊎ ι free-in-ρ ρ₂
         → ι free-in-ρ (ρ₁ ∧ ρ₂)

data _free-in-ε_ {ℓ} ι where
  free-SVar   : ι free-in-ε SVar ι
  free-SLam-τ : ι free-in-τ τ
              → ι free-in-ε SLam τ ε
  free-SLam-ε : suc ι free-in-ε ε
              → ι free-in-ε SLam τ ε
  free-SApp   : ι free-in-ε ε₁ ⊎ ι free-in-ε ε₂
              → ι free-in-ε SApp ε₁ ε₂
  free-SCase  : ∀ {scrut} {branches : CaseBranches nₐ ℓ}
              → ι free-in-ε ε ⊎ ι free-in-branches branches
              → ι free-in-ε SCase scrut branches
  free-SCon   : ∀ {idx : Fin n} {cons : ADTCons (Mkℕₐ n) ℓ}
              → ι free-in-ε ε ⊎ ι free-in-cons cons
              → ι free-in-ε SCon idx ε cons

data _free-in-cons_ {ℓ} ι where
  free-cons-here  : ∀ {cons : ADTCons nₐ ℓ}
                  → ι free-in-τ τ
                  → ι free-in-cons (τ ∷ cons)
  free-cons-there : ∀ {cons : ADTCons nₐ ℓ}
                  → ι free-in-cons cons
                  → ι free-in-cons (τ ∷ cons)

data _free-in-branches_ {ℓ} ι where
  free-branches-here  : ∀ {branches : CaseBranches nₐ ℓ}
                      → suc ι free-in-ε ε
                      → ι free-in-branches (MkCaseBranch ε ∷ branches)
  free-branches-there : ∀ {b} {branches : CaseBranches nₐ ℓ}
                      → ι free-in-branches branches
                      → ι free-in-branches (b ∷ branches)
