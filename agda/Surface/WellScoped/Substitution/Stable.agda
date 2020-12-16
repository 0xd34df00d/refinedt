{-# OPTIONS --safe #-}

module Surface.WellScoped.Substitution.Stable where

open import Data.Fin using (Fin; suc; zero; toℕ; raise)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Fin.Extra
open import Surface.WellScoped
open import Surface.WellScoped.Substitution
import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.FreeVars

