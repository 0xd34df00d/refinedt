{-# OPTIONS --safe #-}

module Intermediate.Translation.Untyped where

open import Data.Vec using (Vec; _∷_; [])

open import Core.Syntax as C
open import Core.Syntax.Derived as C
open import Intermediate.Syntax as I

⌊μ⌋-Τ : CExpr ℓ
⌊μ⌋-Τ = Cunit ≡̂ Cunit of CUnit

⌊μ⌋-b : I.BaseType
      → CExpr ℓ
⌊μ⌋-b BUnit = Σ[ CUnit ] CLam CUnit ⌊μ⌋-Τ
