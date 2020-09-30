{-# OPTIONS --safe #-}

module Common.NamingContext where

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Fin using (Fin; zero; suc; raise)

record NamingCtx : Set where
  constructor MkNamingCtx
  field
    ctx-len : ℕ

open NamingCtx

variable
  n : ℕ
  Γ↓ : NamingCtx

grow-Γ↓ : NamingCtx → NamingCtx
grow-Γ↓ Γ↓ = MkNamingCtx (suc (ctx-len Γ↓))

Var : NamingCtx → Set
Var Γ↓ = Fin (ctx-len Γ↓)

var-eq : Var Γ↓ → Var Γ↓ → Bool
var-eq zero zero = true
var-eq (suc n) (suc m) = var-eq n m
var-eq _ _ = false

closest-var : Var (grow-Γ↓ Γ↓)
closest-var = zero

grow-var : Var Γ↓ → Var (grow-Γ↓ Γ↓)
grow-var var = raise 1 var
