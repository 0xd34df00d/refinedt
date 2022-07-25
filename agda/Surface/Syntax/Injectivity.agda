{-# OPTIONS --safe #-}

module Surface.Syntax.Injectivity where

open import Data.Vec using (Vec; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax

private
  variable
    τ₁₁ τ₁₂ τ₂₁ τ₂₂ : SType ℓ
    ε₁₁ ε₁₂ ε₂₁ ε₂₂ : STerm ℓ
    ρ₁₁ ρ₁₂ ρ₂₁ ρ₂₂ : Refinement ℓ

-- Types
⟨∣⟩-inj₁ : ⟨ b₁ ∣ ρ₁ ⟩ ≡ ⟨ b₂ ∣ ρ₂ ⟩
         → b₁ ≡ b₂
⟨∣⟩-inj₁ refl = refl

⟨∣⟩-inj₂ : ⟨ b₁ ∣ ρ₁ ⟩ ≡ ⟨ b₂ ∣ ρ₂ ⟩
         → ρ₁ ≡ ρ₂
⟨∣⟩-inj₂ refl = refl

⇒-inj₁ : τ₁₁ ⇒ τ₁₂ ≡ τ₂₁ ⇒ τ₂₂
       → τ₁₁ ≡ τ₂₁
⇒-inj₁ refl = refl

⇒-inj₂ : τ₁₁ ⇒ τ₁₂ ≡ τ₂₁ ⇒ τ₂₂
       → τ₁₂ ≡ τ₂₂
⇒-inj₂ refl = refl

⊍-inj-len : ∀ {n₁ n₂}
              {cons₁ : ADTCons (Mkℕₐ n₁) ℓ}
              {cons₂ : ADTCons (Mkℕₐ n₂) ℓ}
          → ⊍ cons₁ ≡ ⊍ cons₂
          → n₁ ≡ n₂
⊍-inj-len refl = refl

⊍-inj-cons : ∀ {cons₁ cons₂ : ADTCons (Mkℕₐ n) ℓ}
           → ⊍ cons₁ ≡ ⊍ cons₂
           → cons₁ ≡ cons₂
⊍-inj-cons refl = refl


-- Refinements
≈-inj₁ : ε₁₁ ≈ ε₁₂ of τ₁ ≡ ε₂₁ ≈ ε₂₂ of τ₂
       → ε₁₁ ≡ ε₂₁
≈-inj₁ refl = refl

≈-inj₂ : ε₁₁ ≈ ε₁₂ of τ₁ ≡ ε₂₁ ≈ ε₂₂ of τ₂
       → ε₁₂ ≡ ε₂₂
≈-inj₂ refl = refl

≈-inj₃ : ε₁₁ ≈ ε₁₂ of τ₁ ≡ ε₂₁ ≈ ε₂₂ of τ₂
       → τ₁ ≡ τ₂
≈-inj₃ refl = refl

∧-inj₁ : ρ₁₁ ∧ ρ₁₂ ≡ ρ₂₁ ∧ ρ₂₂
       → ρ₁₁ ≡ ρ₂₁
∧-inj₁ refl = refl

∧-inj₂ : ρ₁₁ ∧ ρ₁₂ ≡ ρ₂₁ ∧ ρ₂₂
       → ρ₁₂ ≡ ρ₂₂
∧-inj₂ refl = refl


-- Terms
SLam-inj₁ : SLam τ₁ ε₁ ≡ SLam τ₂ ε₂
          → τ₁ ≡ τ₂
SLam-inj₁ refl = refl

SLam-inj₂ : SLam τ₁ ε₁ ≡ SLam τ₂ ε₂
          → ε₁ ≡ ε₂
SLam-inj₂ refl = refl

SApp-inj₁ : SApp ε₁₁ ε₁₂ ≡ SApp ε₂₁ ε₂₂
          → ε₁₁ ≡ ε₂₁
SApp-inj₁ refl = refl

SApp-inj₂ : SApp ε₁₁ ε₁₂ ≡ SApp ε₂₁ ε₂₂
          → ε₁₂ ≡ ε₂₂
SApp-inj₂ refl = refl

SCase-inj-len : ∀ {nₐ₁ nₐ₂}
                  {branches₁ : CaseBranches nₐ₁ ℓ} {cons₁ : ADTCons nₐ₁ ℓ}
                  {branches₂ : CaseBranches nₐ₂ ℓ} {cons₂ : ADTCons nₐ₂ ℓ}
              → SCase ε₁ cons₁ τ₁ branches₁ ≡ SCase ε₂ cons₂ τ₂ branches₂
              → nₐ₁ ≡ nₐ₂
SCase-inj-len refl = refl

SCase-inj₁ : ∀ {nₐ₁ nₐ₂}
               {branches₁ : CaseBranches nₐ₁ ℓ} {cons₁ : ADTCons nₐ₁ ℓ}
               {branches₂ : CaseBranches nₐ₂ ℓ} {cons₂ : ADTCons nₐ₂ ℓ}
           → SCase ε₁ cons₁ τ₁ branches₁ ≡ SCase ε₂ cons₂ τ₂ branches₂
           → ε₁ ≡ ε₂
SCase-inj₁ refl = refl

SCase-inj₂ : ∀ {branches₁ branches₂ : CaseBranches nₐ ℓ}
               {cons₁ cons₂ : ADTCons nₐ ℓ}
           → SCase ε₁ cons₁ τ₁ branches₁ ≡ SCase ε₂ cons₂ τ₂ branches₂
           → cons₁ ≡ cons₂
SCase-inj₂ refl = refl

SCase-inj₃ : ∀ {nₐ₁ nₐ₂}
               {branches₁ : CaseBranches nₐ₁ ℓ} {cons₁ : ADTCons nₐ₁ ℓ}
               {branches₂ : CaseBranches nₐ₂ ℓ} {cons₂ : ADTCons nₐ₂ ℓ}
           → SCase ε₁ cons₁ τ₁ branches₁ ≡ SCase ε₂ cons₂ τ₂ branches₂
           → τ₁ ≡ τ₂
SCase-inj₃ refl = refl

SCase-inj₄ : ∀ {branches₁ branches₂ : CaseBranches nₐ ℓ}
               {cons₁ cons₂ : ADTCons nₐ ℓ}
           → SCase ε₁ cons₁ τ₁ branches₁ ≡ SCase ε₂ cons₂ τ₂ branches₂
           → branches₁ ≡ branches₂
SCase-inj₄ refl = refl

SCon-inj-len : ∀ {n₁ n₂} {ι₁ : Fin n₁} {ι₂ : Fin n₂}
                 {cons₁ : ADTCons (Mkℕₐ n₁) ℓ}
                 {cons₂ : ADTCons (Mkℕₐ n₂) ℓ}
             → SCon ι₁ ε₁ cons₁ ≡ SCon ι₂ ε₂ cons₂
             → n₁ ≡ n₂
SCon-inj-len refl = refl

SCon-inj₁ : ∀ {n} {ι₁ ι₂ : Fin n}
              {cons₁ cons₂ : ADTCons (Mkℕₐ n) ℓ}
            → SCon ι₁ ε₁ cons₁ ≡ SCon ι₂ ε₂ cons₂
            → ι₁ ≡ ι₂
SCon-inj₁ refl = refl

SCon-inj₂ : ∀ {n₁ n₂} {ι₁ : Fin n₁} {ι₂ : Fin n₂}
              {cons₁ : ADTCons (Mkℕₐ n₁) ℓ}
              {cons₂ : ADTCons (Mkℕₐ n₂) ℓ}
            → SCon ι₁ ε₁ cons₁ ≡ SCon ι₂ ε₂ cons₂
            → ε₁ ≡ ε₂
SCon-inj₂ refl = refl

SCon-inj₃ : ∀ {n} {ι₁ ι₂ : Fin n}
              {cons₁ cons₂ : ADTCons (Mkℕₐ n) ℓ}
            → SCon ι₁ ε₁ cons₁ ≡ SCon ι₂ ε₂ cons₂
            → cons₁ ≡ cons₂
SCon-inj₃ refl = refl

∷-inj₁ : ∀ {A : Set} {a b : A} {as bs : Vec A n}
       → a ∷ as ≡ b ∷ bs
       → a ≡ b
∷-inj₁ refl = refl

∷-inj₂ : ∀ {A : Set} {a b : A} {as bs : Vec A n}
       → a ∷ as ≡ b ∷ bs
       → as ≡ bs
∷-inj₂ refl = refl

CaseBranch-inj : ∀ {ε₁ ε₂ : STerm (suc ℓ)}
               → MkCaseBranch ε₁ ≡ MkCaseBranch ε₂
               → ε₁ ≡ ε₂
CaseBranch-inj refl = refl
