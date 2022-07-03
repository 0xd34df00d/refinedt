{-# OPTIONS --safe #-}

module Surface.Derivations.Declarative.Theorems.Helpers where

open import Surface.Syntax
open import Surface.Derivations.Declarative

Γok-tail : (Γ , τ) ok[ θ , φ ] → Γ ok[ θ , φ ]
Γok-tail (TCTX-Bind prev _) = prev

Γok-head : (Γ , τ) ok[ θ , φ ] → Γ ⊢[ θ , φ ] τ
Γok-head (TCTX-Bind _ δ) = δ

arr-wf-⇒-cod-wf : Γ ⊢[ θ , φ ] τ₁ ⇒ τ₂
                → Γ , τ₁ ⊢[ θ , φ ] τ₂
arr-wf-⇒-cod-wf (TWF-Arr _ δ) = δ
