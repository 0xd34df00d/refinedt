{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Helpers where

open import Surface.Syntax
open import Surface.Derivations.Algorithmic

Γok-tail : (Γ , τ) ok[ φ ] → Γ ok[ φ ]
Γok-tail (TCTX-Bind prev _) = prev

Γok-head : (Γ , τ) ok[ φ ] → Γ ⊢[ φ ] τ
Γok-head (TCTX-Bind _ δ) = δ
