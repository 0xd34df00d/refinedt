-- {-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Surface.Theorems.Thinning.WF where

open import Data.Nat.Base
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Data.Fin.Base using (zero; suc)
open import Data.Fin.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Surface.Syntax
open import Surface.Derivations
import      Surface.Theorems.Agreement.Γok.WF as B
open import Surface.Theorems.Agreement.TypeWellFormedness.WF
open import Surface.Theorems.Thinning
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Membership
open import Surface.Syntax.Renaming as R

{-
lemma' : (Γ⊂Γ' : Γ ⊂' Γ')
       → (Γok : Γ ok)
       → (∈ : τ ∈ Γ at ι)
       → (Γ'ok : Γ' ok)
       → (τ'-≡ : τ' ≡ act-τ (_⊂'_.ρ Γ⊂Γ') τ)
       → (ι'-≡ : ι' ≡ _⊂'_.ρ Γ⊂Γ' ι)
       → (let ∈' = _⊂'_.ρ-∈ Γ⊂Γ' ∈ τ'-≡ ι'-≡)
       → size-∈ Γ'ok ∈' ≤ size-ok Γok ⊔ size-twf τδ + suc (size-ok Γ'ok ⊔ size-twf τ'δ)
lemma' = {! !}
-}

lemma : (Γ⊂Γ' : Γ ⊂' Γ')
      → (Γok : Γ ok)
      → (∈ : τ ∈ Γ at ι)
      → (Γ'ok : Γ' ok)
      → (τ'-≡ : τ' ≡ act-τ (_⊂'_.ρ Γ⊂Γ') τ)
      → (ι'-≡ : ι' ≡ _⊂'_.ρ Γ⊂Γ' ι)
      → (let ∈' = _⊂'_.ρ-∈ Γ⊂Γ' ∈ τ'-≡ ι'-≡)
      → size-∈ Γ'ok ∈' ≤ size-∈ Γok ∈ + size-ok Γ'ok
lemma (MkTR ρ ρ-∈ ρ-mono) (TCTX-Bind Γok τδ) (∈-zero refl) (TCTX-Bind Γ'ok τ'δ) τ'-≡ ι'-≡ with ρ-∈ (∈-zero refl) τ'-≡ ι'-≡
... | ∈-zero refl = s≤s {! !}
... | ∈-suc refl ∈' = s≤s {! !}
lemma (MkTR ρ ρ-∈ ρ-mono) (TCTX-Bind Γok τδ) (∈-suc refl ∈) (TCTX-Bind Γ'ok τ'δ) τ'-≡ ι'-≡ with ρ-∈ (∈-suc refl ∈) τ'-≡ ι'-≡
... | ∈-zero refl = {! impossible, prove later !}
... | ∈-suc refl ∈' = let rec = lemma {! !} Γok ∈ Γ'ok refl refl in s≤s {! !}

mutual
  twf-thinning-sized-size : (Γ⊂Γ' : Γ ⊂ Γ')
                          → (Γ'ok : Γ' ok)
                          → (δ : Γ ⊢ τ)
                          → (acc : Acc _<_ (B.size-twf δ))
                          → size-twf (twf-thinning-sized Γ⊂Γ' Γ'ok δ acc)
                            ≤
                            size-twf δ + size-ok Γ'ok
  twf-thinning-sized-size Γ⊂Γ' Γ'ok (TWF-TrueRef Γok') _ = s≤s (m≤n+m _ _)
  twf-thinning-sized-size Γ⊂Γ' Γ'ok (TWF-Base ε₁δ ε₂δ) (acc rec) = {! !}
  twf-thinning-sized-size Γ⊂Γ' Γ'ok (TWF-Conj ρ₁ ρ₂) (acc rec)
    = let rec₁ = rec _ (s≤s (m≤m⊕n _ _))
          rec₂ = rec _ (s≤s (n≤m⊕n _ _))
          size₁ = twf-thinning-sized-size Γ⊂Γ' Γ'ok ρ₁ rec₁
          size₂ = twf-thinning-sized-size Γ⊂Γ' Γ'ok ρ₂ rec₂
       in s≤s {! !}
  twf-thinning-sized-size Γ⊂Γ' Γ'ok (TWF-Arr δ δ₁) (acc rec) = {! !}
  twf-thinning-sized-size Γ⊂Γ' Γ'ok (TWF-ADT consδs) (acc rec) = {! !}

  t-thinning-sized-size : (Γ⊂Γ' : Γ ⊂ Γ')
                        → (Γ'ok : Γ' ok)
                        → (δ : Γ ⊢ ε ⦂ τ)
                        → (acc : Acc _<_ (B.size-t δ))
                        → size-t (t-thinning-sized Γ⊂Γ' Γ'ok δ acc) ≤ size-t δ + size-ok Γ'ok
  t-thinning-sized-size Γ⊂Γ' Γ'ok (T-Unit Γok) _ = s≤s (s≤s (m≤n+m _ _))
  t-thinning-sized-size Γ⊂Γ' Γ'ok (T-Var Γok ∈) _
    rewrite m≤n⇒m⊔n≡n (size-ok-≤-size-∈ Γok ∈)
          = s≤s {! !}
  t-thinning-sized-size Γ⊂Γ' Γ'ok (T-Abs arrδ δ) (acc rec) = {! !}
  t-thinning-sized-size Γ⊂Γ' Γ'ok (T-App δ δ₁) (acc rec) = {! !}
  t-thinning-sized-size Γ⊂Γ' Γ'ok (T-Case resδ δ branches-well-typed) (acc rec) = {! !}
  t-thinning-sized-size Γ⊂Γ' Γ'ok (T-Con ≡-prf δ adtτ) (acc rec) = {! !}
  t-thinning-sized-size Γ⊂Γ' Γ'ok (T-Sub δ τ'δ <:) (acc rec) = {! !}
  t-thinning-sized-size Γ⊂Γ' Γ'ok (T-RConv δ τ'δ τ~τ') (acc rec) = {! !}

twf-thinning-size : (Γ⊂Γ' : Γ ⊂ Γ')
                  → (Γ'ok : Γ' ok)
                  → (δ : Γ ⊢ τ)
                  → size-twf (twf-thinning Γ⊂Γ' Γ'ok δ) ≤ size-twf δ + size-ok Γ'ok
twf-thinning-size Γ⊂Γ' Γ'ok δ = twf-thinning-sized-size Γ⊂Γ' Γ'ok δ (<-wellFounded _)

twf-weakening-size : (Γok : Γ ok)
                   → (Γ⊢τ' : Γ ⊢ τ')
                   → (Γ⊢τ : Γ ⊢ τ)
                   → size-twf (twf-weakening Γok Γ⊢τ' Γ⊢τ)
                     ≤
                     size-twf Γ⊢τ + suc (size-ok Γok ⊕ size-twf Γ⊢τ')
twf-weakening-size Γok Γ⊢τ' Γ⊢τ = twf-thinning-size (ignore-head ⊂-refl) (TCTX-Bind Γok Γ⊢τ') Γ⊢τ
