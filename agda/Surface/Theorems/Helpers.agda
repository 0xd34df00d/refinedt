module Surface.Theorems.Helpers where

open import Data.Nat.Properties

open import Surface.Syntax
open import Surface.Derivations
open import Surface.Derivations.WF

Γok-tail : (Γ , x ⦂ τ) ok → Γ ok
Γok-tail (TCTX-Bind prev _) = prev

Γok-head : (Γ , x ⦂ τ) ok → Γ ⊢ τ
Γok-head (TCTX-Bind _ δ) = δ

Γok-tail-smaller : (δ : (Γ , x ⦂ τ) ok) → size-ok (Γok-tail δ) < size-ok δ
Γok-tail-smaller (TCTX-Bind prevOk τδ) = s≤s (m≤m<>n (size-ok prevOk) (size-twf τδ))

Γok-head-smaller : (δ : (Γ , x ⦂ τ) ok) → size-twf (Γok-head δ) < size-ok δ
Γok-head-smaller (TCTX-Bind prevOk τδ) = s≤s (n≤m<>n (size-ok prevOk) (size-twf τδ))

arr-wf-⇒-cod-wf : Γ ⊢ SArr x τ₁ τ₂ → Γ , x ⦂ τ₁ ⊢ τ₂
arr-wf-⇒-cod-wf (TWF-Arr _ δ) = δ
