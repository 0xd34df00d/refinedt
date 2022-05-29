-- {-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Surface.Derivations.Declarative.Theorems.Thinning.WF where

open import Data.Nat.Base
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Data.Fin.Base using (zero; suc)
open import Data.Fin.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Surface.Syntax
open import Surface.Derivations.Declarative
open import Surface.Derivations.Declarative.Theorems.Agreement.TypeWellFormedness.WF
open import Surface.Derivations.Declarative.Theorems.Thinning
open import Surface.Syntax.Membership
open import Surface.Syntax.Subcontext
open import Surface.Syntax.Renaming as R

{-
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
-}

n₁≤suc[n₂]⇒m+n₁≤n₂+suc[m] : ∀ n₁ n₂ m
                          → n₁ ≤ suc n₂
                          → m + n₁ ≤ n₂ + suc m
n₁≤suc[n₂]⇒m+n₁≤n₂+suc[m] = {! !}

lemma : (Γ⊂Γ' : k by Γ ⊂' Γ')
      → (∈ : τ ∈ Γ at ι)
      → (Γok : Γ ok)
      → (Γ'ok : Γ' ok)
      → size-∈ Γ'ok (∈-thinning Γ⊂Γ' ∈) ≤ size-∈ Γok ∈ + size-ok Γ'ok
lemma ignore-head (∈-zero refl) (TCTX-Bind Γok τδ) (TCTX-Bind (TCTX-Bind Γ'ok τδ₂) τδ₁) = s≤s (n₁≤suc[n₂]⇒m+n₁≤n₂+suc[m] _ _ _ (s≤s {! !}))
lemma ignore-head (∈-suc refl ∈) (TCTX-Bind Γok τδ) (TCTX-Bind (TCTX-Bind Γ'ok τδ₂) τδ₁) = s≤s (n₁≤suc[n₂]⇒m+n₁≤n₂+suc[m] _ _ _ (s≤s {! !}))
lemma (append-both Γ⊂Γ') (∈-zero refl) (TCTX-Bind Γok τδ) (TCTX-Bind Γ'ok τδ₁) = {! !}
lemma (append-both Γ⊂Γ') (∈-suc refl ∈) (TCTX-Bind Γok τδ) (TCTX-Bind Γ'ok τδ₁) = {! !}

mutual
  Γ⊢τ-thinning-size : (Γ⊂Γ' : k by Γ ⊂' Γ')
                    → (Γ'ok : Γ' ok)
                    → (δ : Γ ⊢ τ)
                    → size-twf (Γ⊢τ-thinning Γ⊂Γ' Γ'ok δ)
                      ≤
                      size-twf δ + size-ok Γ'ok
  Γ⊢τ-thinning-size Γ⊂Γ' Γ'ok (TWF-TrueRef _) = s≤s (m≤n+m _ _)
  Γ⊢τ-thinning-size Γ⊂Γ' Γ'ok (TWF-Base ε₁δ ε₂δ) = {! !}
  Γ⊢τ-thinning-size Γ⊂Γ' Γ'ok (TWF-Conj δ δ₁) = {! !}
  Γ⊢τ-thinning-size Γ⊂Γ' Γ'ok (TWF-Arr δ δ₁) = {! !}
  Γ⊢τ-thinning-size Γ⊂Γ' Γ'ok (TWF-ADT consδs) = {! !}

  Γ⊢ε⦂τ-thinning-size : (Γ⊂Γ' : k by Γ ⊂' Γ')
                      → (Γ'ok : Γ' ok)
                      → (δ : Γ ⊢ ε ⦂ τ)
                      → size-t (Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok δ)
                        ≤
                        size-t δ + size-ok Γ'ok
  Γ⊢ε⦂τ-thinning-size Γ⊂Γ' Γ'ok (T-Unit Γok) = s≤s (s≤s (m≤n+m _ _))
  Γ⊢ε⦂τ-thinning-size Γ⊂Γ' Γ'ok (T-Var Γok ∈)
    rewrite m≤n⇒m⊔n≡n (size-ok-≤-size-∈ Γok ∈)
          = s≤s {! !}
  Γ⊢ε⦂τ-thinning-size Γ⊂Γ' Γ'ok (T-Abs arrδ δ) = {! !}
  Γ⊢ε⦂τ-thinning-size Γ⊂Γ' Γ'ok (T-App δ δ₁) = {! !}
  Γ⊢ε⦂τ-thinning-size Γ⊂Γ' Γ'ok (T-Case resδ δ branches-well-typed) = {! !}
  Γ⊢ε⦂τ-thinning-size Γ⊂Γ' Γ'ok (T-Con ≡-prf δ adtτ) = {! !}
  Γ⊢ε⦂τ-thinning-size Γ⊂Γ' Γ'ok (T-Sub δ τ'δ <:) = {! !}
  Γ⊢ε⦂τ-thinning-size Γ⊂Γ' Γ'ok (T-RConv δ τ'δ τ~τ') = {! !}

Γ⊢τ-weakening-size : (Γok : Γ ok)
                   → (Γ⊢τ' : Γ ⊢ τ')
                   → (Γ⊢τ : Γ ⊢ τ)
                   → size-twf (Γ⊢τ-weakening Γok Γ⊢τ' Γ⊢τ)
                     ≤
                     size-twf Γ⊢τ + suc (size-ok Γok ⊕ size-twf Γ⊢τ')
Γ⊢τ-weakening-size Γok Γ⊢τ' Γ⊢τ = Γ⊢τ-thinning-size ignore-head (TCTX-Bind Γok Γ⊢τ') Γ⊢τ
