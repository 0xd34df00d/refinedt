{-# OPTIONS --safe #-}

module Core.Syntax.Derived.Actions where

open import Data.Fin using (zero; suc)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Common.Helpers
open import Core.Syntax
open import Core.Syntax.Renaming
open import Core.Syntax.Renaming.Distributivity
open import Core.Syntax.Derived

ext-f∘suc-≡-suc∘f : ∀ (f : Fin ℓ → Fin ℓ')
                  → act-ε (ext f) ∘ act-ε suc f≡ act-ε suc ∘ act-ε f
ext-f∘suc-≡-suc∘f f ε
  rewrite act-ε-distr suc (ext f) ε
        | act-ε-distr f suc ε
        = refl

act-Σ-commutes : ∀ (f : Fin ℓ → Fin ℓ') τ P
               → act-ε f (Σ[ τ ] P) ≡ Σ[ act-ε f τ ] (act-ε f P)
act-Σ-commutes f τ P
  rewrite ext-f∘suc-≡-suc∘f f τ
        | act-ε-distr suc suc P
        | act-ε-distr (λ x → suc (suc x)) (ext (ext f)) P
        | act-ε-distr f suc P
        | act-ε-distr (λ x → suc (f x)) suc P
        = refl
