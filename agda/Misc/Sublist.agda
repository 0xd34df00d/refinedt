{-# OPTIONS --safe #-}

module Misc.Sublist where

open import Agda.Builtin.Equality
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List

data _⊂_ {a : Set} : (xs xs' : List a) → Set where
  EmptyIsSublist  : ∀ {xs'} → [] ⊂ xs'
  IgnoreHead      : ∀ {xs xs' x}
                  → xs ⊂ xs'
                  → xs ⊂ (x ∷ xs')
  PrependBoth     : ∀ {xs xs' x}
                  → xs ⊂ xs'
                  → (x ∷ xs) ⊂ (x ∷ xs')

abstract
  ⊂-refl : {a : Set} → (xs : List a) → xs ⊂ xs
  ⊂-refl [] = EmptyIsSublist
  ⊂-refl (x ∷ xs) = PrependBoth (⊂-refl xs)

  ⊂-preserves-∈ : ∀ {a xs xs'} {x : a}
                → xs ⊂ xs'
                → x ∈ xs
                → x ∈ xs'
  ⊂-preserves-∈ (IgnoreHead ⊂-tail) ∈-prf = there (⊂-preserves-∈ ⊂-tail ∈-prf)
  ⊂-preserves-∈ (PrependBoth ⊂-tail) (here px) = here px
  ⊂-preserves-∈ (PrependBoth ⊂-tail) (there ∈-rest) = there (⊂-preserves-∈ ⊂-tail ∈-rest)
