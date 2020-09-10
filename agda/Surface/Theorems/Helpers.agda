module Surface.Theorems.Helpers where

open import Surface.Syntax
open import Surface.Derivations

Γok-tail : (Γ , x ⦂ τ) ok → Γ ok
Γok-tail (TCTX-Bind prev _) = prev

Γok-head : (Γ , x ⦂ τ) ok → Γ ⊢ τ
Γok-head (TCTX-Bind _ δ) = δ
