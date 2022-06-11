{-# OPTIONS --safe #-}

module Intermediate.Syntax.Injectivity where

open import Data.Vec using (Vec; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Intermediate.Syntax

private
  variable
    τ₁₁ τ₁₂ τ₂₁ τ₂₂ : IType ℓ
    ε₁₁ ε₁₂ ε₂₁ ε₂₂ : ITerm ℓ
    ρ₁₁ ρ₁₂ ρ₂₁ ρ₂₂ : IRefinement ℓ

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


-- IRefinements
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
ILam-inj₁ : ILam τ₁ ε₁ ≡ ILam τ₂ ε₂
          → τ₁ ≡ τ₂
ILam-inj₁ refl = refl

ILam-inj₂ : ILam τ₁ ε₁ ≡ ILam τ₂ ε₂
          → ε₁ ≡ ε₂
ILam-inj₂ refl = refl

IApp-inj₁ : IApp ε₁₁ ε₁₂ ≡ IApp ε₂₁ ε₂₂
          → ε₁₁ ≡ ε₂₁
IApp-inj₁ refl = refl

IApp-inj₂ : IApp ε₁₁ ε₁₂ ≡ IApp ε₂₁ ε₂₂
          → ε₁₂ ≡ ε₂₂
IApp-inj₂ refl = refl

ICase-inj-len : ∀ {nₐ₁ nₐ₂}
                  {branches₁ : CaseBranches nₐ₁ ℓ}
                  {branches₂ : CaseBranches nₐ₂ ℓ}
              → ICase ε₁ branches₁ ≡ ICase ε₂ branches₂
              → nₐ₁ ≡ nₐ₂
ICase-inj-len refl = refl

ICase-inj₁ : ∀ {nₐ₁ nₐ₂}
               {branches₁ : CaseBranches nₐ₁ ℓ}
               {branches₂ : CaseBranches nₐ₂ ℓ}
           → ICase ε₁ branches₁ ≡ ICase ε₂ branches₂
           → ε₁ ≡ ε₂
ICase-inj₁ refl = refl

ICase-inj₂ : ∀ {branches₁ branches₂ : CaseBranches nₐ ℓ}
           → ICase ε₁ branches₁ ≡ ICase ε₂ branches₂
           → branches₁ ≡ branches₂
ICase-inj₂ refl = refl

ICon-inj-len : ∀ {n₁ n₂} {ι₁ : Fin n₁} {ι₂ : Fin n₂}
                 {cons₁ : ADTCons (Mkℕₐ n₁) ℓ}
                 {cons₂ : ADTCons (Mkℕₐ n₂) ℓ}
             → ICon ι₁ ε₁ cons₁ ≡ ICon ι₂ ε₂ cons₂
             → n₁ ≡ n₂
ICon-inj-len refl = refl

ICon-inj₁ : ∀ {n} {ι₁ ι₂ : Fin n}
              {cons₁ cons₂ : ADTCons (Mkℕₐ n) ℓ}
            → ICon ι₁ ε₁ cons₁ ≡ ICon ι₂ ε₂ cons₂
            → ι₁ ≡ ι₂
ICon-inj₁ refl = refl

ICon-inj₂ : ∀ {n₁ n₂} {ι₁ : Fin n₁} {ι₂ : Fin n₂}
              {cons₁ : ADTCons (Mkℕₐ n₁) ℓ}
              {cons₂ : ADTCons (Mkℕₐ n₂) ℓ}
            → ICon ι₁ ε₁ cons₁ ≡ ICon ι₂ ε₂ cons₂
            → ε₁ ≡ ε₂
ICon-inj₂ refl = refl

ICon-inj₃ : ∀ {n} {ι₁ ι₂ : Fin n}
              {cons₁ cons₂ : ADTCons (Mkℕₐ n) ℓ}
            → ICon ι₁ ε₁ cons₁ ≡ ICon ι₂ ε₂ cons₂
            → cons₁ ≡ cons₂
ICon-inj₃ refl = refl

I<:-inj₁ : ε₁ I<: τ₁ ≡ ε₂ I<: τ₂
         → ε₁ ≡ ε₂
I<:-inj₁ refl = refl

I<:-inj₂ : ε₁ I<: τ₁ ≡ ε₂ I<: τ₂
         → τ₁ ≡ τ₂
I<:-inj₂ refl = refl

∷-inj₁ : ∀ {A : Set} {a b : A} {as bs : Vec A n}
       → a ∷ as ≡ b ∷ bs
       → a ≡ b
∷-inj₁ refl = refl

∷-inj₂ : ∀ {A : Set} {a b : A} {as bs : Vec A n}
       → a ∷ as ≡ b ∷ bs
       → as ≡ bs
∷-inj₂ refl = refl

CaseBranch-inj : ∀ {ε₁ ε₂ : ITerm (suc ℓ)}
               → MkCaseBranch ε₁ ≡ MkCaseBranch ε₂
               → ε₁ ≡ ε₂
CaseBranch-inj refl = refl
