{-# OPTIONS --safe #-}

module Core.Syntax.Membership where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Core.Syntax
open import Core.Syntax.Renaming as R

infix 4 _∈_at_
data _∈_at_ : CExpr ℓ → Ctx ℓ → Fin ℓ → Set where
  ∈-zero : (≡-prf : τ₀ ≡ R.weaken-ε τ)
         → τ₀ ∈ Γ , τ at zero
  ∈-suc  : (≡-prf : τ₀ ≡ R.weaken-ε τ)
         → (there : τ ∈ Γ at ι)
         → τ₀ ∈ Γ , τ' at suc ι
