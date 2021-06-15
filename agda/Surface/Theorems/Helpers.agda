{-# OPTIONS --safe #-}

module Surface.Theorems.Helpers where

open import Surface.Syntax
open import Surface.Derivations

Γok-tail : (Γ , τ) ok → Γ ok
Γok-tail (TCTX-Bind prev _) = prev

Γok-head : (Γ , τ) ok → Γ ⊢ τ
Γok-head (TCTX-Bind _ δ) = δ

arr-wf-⇒-cod-wf : Γ ⊢ τ₁ ⇒ τ₂
                → Γ , τ₁ ⊢ τ₂
arr-wf-⇒-cod-wf (TWF-Arr _ δ) = δ

arr-wf-⇒-dom-wf : Γ ⊢ τ₁ ⇒ τ₂
                → Γ ⊢ τ₁
arr-wf-⇒-dom-wf (TWF-Arr δ _) = δ
