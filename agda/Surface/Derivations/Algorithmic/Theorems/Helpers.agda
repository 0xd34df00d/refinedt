{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Helpers where

open import Surface.Syntax
open import Surface.Derivations.Algorithmic

Γok-tail : (Γ , τ) ok[ φ ] → Γ ok[ φ ]
Γok-tail (TCTX-Bind prev _) = prev

Γok-head : (Γ , τ) ok[ φ ] → Γ ⊢[ φ ] τ
Γok-head (TCTX-Bind _ δ) = δ

arr-wf-⇒-cod-wf : Γ ⊢[ φ ] τ₁ ⇒ τ₂
                → Γ , τ₁ ⊢[ φ ] τ₂
arr-wf-⇒-cod-wf (TWF-Arr _ δ) = δ

arr-wf-⇒-dom-wf : Γ ⊢[ φ ] τ₁ ⇒ τ₂
                → Γ ⊢[ φ ] τ₁
arr-wf-⇒-dom-wf (TWF-Arr δ _) = δ