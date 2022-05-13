{-# OPTIONS --safe #-}

module Intermediate.Derivations.Algorithmic.Theorems.Helpers where

open import Intermediate.Syntax
open import Intermediate.Derivations.Algorithmic

Γok-tail : [ θ ] (Γ , τ) ok → [ θ ] Γ ok
Γok-tail (TCTX-Bind prev _) = prev

Γok-head : [ θ ] (Γ , τ) ok → [ θ ] Γ ⊢ τ
Γok-head (TCTX-Bind _ δ) = δ

dom-well-formed : [ θ ] Γ ⊢ τ₁ ⇒ τ₂
                → [ θ ] Γ ⊢ τ₁
dom-well-formed (TWF-Arr τ₁δ _) = τ₁δ
