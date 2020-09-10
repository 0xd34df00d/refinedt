module Surface.Theorems.Helpers where

open import Surface.Syntax
open import Surface.Derivations

Γok-tail : (Γ , x ⦂ τ) ok → Γ ok
Γok-tail (TCTX-Bind prev _) = prev
