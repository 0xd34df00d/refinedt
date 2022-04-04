{-# OPTIONS --safe #-}

module Intermediate.Derivations.Algorithmic.Theorems.Helpers where

open import Intermediate.Syntax
open import Intermediate.Derivations.Algorithmic

Γok-tail : [ θ ] (Γ , τ) ok → [ θ ] Γ ok
Γok-tail (TCTX-Bind prev _) = prev

Γok-head : [ θ ] (Γ , τ) ok → [ θ ] Γ ⊢ τ
Γok-head (TCTX-Bind _ δ) = δ
