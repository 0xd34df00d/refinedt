{-# OPTIONS --safe #-}

{- We prove our language is "useful" by showing that it is non-empty, and there are some useful typeable terms -}

module Surface.Useful where

open import Data.Product renaming (_,_ to ⟨_,_⟩)

open import Surface.Syntax
open import Surface.Derivations

Typeable : STerm 0 → Set
Typeable ε = Σ (SType 0) (λ τ → ⊘ ⊢ ε ⦂ τ)

SUnit-Typeable : Typeable SUnit
SUnit-Typeable = ⟨ ⟨ BUnit ∣ SUnit ≈ SUnit of BUnit ⟩ , T-Unit TCTX-Empty ⟩
