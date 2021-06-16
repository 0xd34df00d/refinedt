-- {-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Surface.Theorems.Thinning.WF where

open import Data.Nat.Base
open import Data.Nat.Induction
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Surface.Syntax
open import Surface.Derivations
import      Surface.Theorems.Agreement.Γok.WF as B
open import Surface.Theorems.Agreement.TypeWellFormedness.WF
open import Surface.Theorems.Thinning
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Membership

mutual
  twf-thinning-sized-size : (Γ⊂Γ' : Γ ⊂ Γ')
                          → (Γ'ok : Γ' ok)
                          → (δ : Γ ⊢ τ)
                          → (acc : Acc _<_ (B.size-twf δ))
                          → size-twf (twf-thinning-sized Γ⊂Γ' Γ'ok δ acc)
                            ≤
                            size-ok Γ'ok + size-twf δ
  twf-thinning-sized-size Γ⊂Γ' Γ'ok (TWF-TrueRef Γok') _ = {! !} -- s≤s (m≤m⊕n _ _)
  twf-thinning-sized-size Γ⊂Γ' Γ'ok (TWF-Base ε₁δ ε₂δ) (acc rec) = {! !}
  twf-thinning-sized-size Γ⊂Γ' Γ'ok (TWF-Conj ρ₁ ρ₂) (acc rec)
    = let rec₁ = rec _ (s≤s (m≤m⊕n _ _))
          rec₂ = rec _ (s≤s (n≤m⊕n _ _))
          size₁ = twf-thinning-sized-size Γ⊂Γ' Γ'ok ρ₁ rec₁
          size₂ = twf-thinning-sized-size Γ⊂Γ' Γ'ok ρ₂ rec₂
       in {! !}
  twf-thinning-sized-size Γ⊂Γ' Γ'ok (TWF-Arr δ δ₁) (acc rec) = {! !}
  twf-thinning-sized-size Γ⊂Γ' Γ'ok (TWF-ADT consδs) (acc rec) = {! !}

  t-thinning-sized-size : (Γ⊂Γ' : Γ ⊂ Γ')
                        → (Γ'ok : Γ' ok)
                        → (δ : Γ ⊢ ε ⦂ τ)
                        → (acc : Acc _<_ (B.size-t δ))
                        → size-t (t-thinning-sized Γ⊂Γ' Γ'ok δ acc) ≤ {! !}
  t-thinning-sized-size Γ⊂Γ' Γ'ok (T-Unit Γok) _ = {! !}
  t-thinning-sized-size Γ⊂Γ' Γ'ok (T-Var Γok x) _ = {! !}
  t-thinning-sized-size Γ⊂Γ' Γ'ok (T-Abs arrδ δ) (acc rec) = {! !}
  t-thinning-sized-size Γ⊂Γ' Γ'ok (T-App δ δ₁) (acc rec) = {! !}
  t-thinning-sized-size Γ⊂Γ' Γ'ok (T-Case resδ δ branches-well-typed) (acc rec) = {! !}
  t-thinning-sized-size Γ⊂Γ' Γ'ok (T-Con ≡-prf δ adtτ) (acc rec) = {! !}
  t-thinning-sized-size Γ⊂Γ' Γ'ok (T-Sub δ τ'δ <:) (acc rec) = {! !}
  t-thinning-sized-size Γ⊂Γ' Γ'ok (T-RConv δ τ'δ τ~τ') (acc rec) = {! !}

twf-thinning-size : (Γ⊂Γ' : Γ ⊂ Γ')
                  → (Γ'ok : Γ' ok)
                  → (δ : Γ ⊢ τ)
                  → size-twf (twf-thinning Γ⊂Γ' Γ'ok δ) ≤ size-ok Γ'ok + size-twf δ
twf-thinning-size Γ⊂Γ' Γ'ok δ = twf-thinning-sized-size Γ⊂Γ' Γ'ok δ (<-wellFounded _)

twf-weakening-size : (Γok : Γ ok)
                   → (Γ⊢τ' : Γ ⊢ τ')
                   → (Γ⊢τ : Γ ⊢ τ)
                   → size-twf (twf-weakening Γok Γ⊢τ' Γ⊢τ)
                     ≤
                     suc (size-ok Γok ⊕ size-twf Γ⊢τ') + size-twf Γ⊢τ
twf-weakening-size Γok Γ⊢τ' Γ⊢τ = twf-thinning-size (ignore-head ⊂-refl) (TCTX-Bind Γok Γ⊢τ') Γ⊢τ
