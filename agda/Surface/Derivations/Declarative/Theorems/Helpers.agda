{-# OPTIONS --safe #-}

module Surface.Derivations.Declarative.Theorems.Helpers where

open import Surface.Syntax
open import Surface.Derivations.Declarative

Γok-tail : (Γ , τ) ok[ θ ] → Γ ok[ θ ]
Γok-tail (TCTX-Bind prev _) = prev

Γok-head : (Γ , τ) ok[ θ ] → Γ ⊢[ θ ] τ
Γok-head (TCTX-Bind _ δ) = δ

arr-wf-⇒-cod-wf : Γ ⊢[ θ ] τ₁ ⇒ τ₂
                → Γ , τ₁ ⊢[ θ ] τ₂
arr-wf-⇒-cod-wf (TWF-Arr _ δ) = δ
