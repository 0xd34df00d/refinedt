{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Helpers where

open import Surface.Syntax
open import Surface.Derivations.Algorithmic

Γok-tail : (Γ , τ) ok[ θ , φ ] → Γ ok[ θ , φ ]
Γok-tail (TCTX-Bind prev _) = prev

Γok-head : (Γ , τ) ok[ θ , φ ] → Γ ⊢[ θ , φ ] τ
Γok-head (TCTX-Bind _ δ) = δ
