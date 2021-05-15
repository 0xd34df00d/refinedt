{-# OPTIONS --safe #-}

{- We prove our language is "useful" by showing that it is non-empty, and there are some useful typeable terms -}

module Surface.Useful where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Derivations

Typeable : STerm 0 → Set
Typeable ε = Σ (SType 0) (λ τ → ⊘ ⊢ ε ⦂ τ)

unit : SType 0
unit = ⟨ BUnit ∣ SUnit ≈ SUnit of BUnit ⟩

unit-typeable : ⊘ ⊢ SUnit ⦂ unit
unit-typeable = T-Unit TCTX-Empty


bool-cons : ADTCons (Mkℕₐ 2) 0
bool-cons = unit ∷ unit ∷ []

bool : SType 0
bool = ⊍ bool-cons

bool-wf : ⊘ ⊢ bool
bool-wf = TWF-ADT (TWF-TrueRef TCTX-Empty ∷ TWF-TrueRef TCTX-Empty ∷ [])

false : STerm 0
false = SCon zero SUnit bool-cons

true : STerm 0
true = SCon (suc zero) SUnit bool-cons

false-typeable : ⊘ ⊢ false ⦂ bool
false-typeable = T-Con refl unit-typeable bool-wf

true-typeable : ⊘ ⊢ true ⦂ bool
true-typeable = T-Con refl unit-typeable bool-wf


not : STerm 0
not = SLam bool (SCase (SVar zero)
        (MkCaseBranch (weaken-ε-k 2 true)
       ∷ MkCaseBranch (weaken-ε-k 2 false)
       ∷ []))
