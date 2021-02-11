-- {-# OPTIONS --safe #-}

open import Core.Syntax

module Core.Syntax.Actions (α : VarAction) where

open import Data.Vec

open VarAction α public

var-action-record : VarAction
var-action-record = α

ActionOn : (ℕ → Set) → Set
ActionOn Ty = ∀ {ℓ ℓ'} → (Fin ℓ → Target ℓ') → Ty ℓ → Ty ℓ'

act-ε : ActionOn CExpr
act-cons : ActionOn (ADTCons nₐ)
act-branches : ActionOn (CaseBranches nₐ)

act-ε f (CVar ι) = var-action (f ι)
act-ε f (CSort s) = CSort s
act-ε f (CΠ τ₁ τ₂) = CΠ (act-ε f τ₁) (act-ε (ext f) τ₂)
act-ε f (CLam τ ε) = CLam (act-ε f τ) (act-ε (ext f) ε)
act-ε f (CApp ε₁ ε₂) = CApp (act-ε f ε₁) (act-ε f ε₂)
act-ε f Cunit = Cunit
act-ε f CUnit = CUnit
act-ε f (CADT cons) = CADT (act-cons f cons)
act-ε f (CCon ι ε cons) = CCon ι (act-ε f ε) (act-cons f cons)
act-ε f (CCase ε branches) = CCase (act-ε f ε) (act-branches f branches)

act-cons f [] = []
act-cons f (ε ∷ εs) = act-ε f ε ∷ act-cons f εs

act-branches f [] = []
act-branches f (ε ∷ bs) = act-ε (ext (ext f)) ε ∷ act-branches f bs
