{-# OPTIONS --safe #-}

module Surface.Translation.Untyped where

open import Data.Vec using (Vec; _∷_; [])

open import Core.Syntax as C
open import Core.Syntax.Derived as C
open import Surface.Syntax as S

⌊μ⌋-Τ : CExpr ℓ
⌊μ⌋-Τ = Cunit ≡̂ Cunit of CUnit

⌊μ⌋-b : S.BaseType
      → CExpr ℓ
⌊μ⌋-b BUnit = Σ[ CUnit ] CLam CUnit ⌊μ⌋-Τ
