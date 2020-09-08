module Sublist where

open import Data.List

data _⊂_ {a : Set} : (xs xs' : List a) → Set where
  EmptyIsSublist  : ∀ {xs'} → [] ⊂ xs'
  IgnoreHead      : ∀ {xs xs' x}
                  → xs ⊂ xs'
                  → xs ⊂ (x ∷ xs')
  PrependBoth     : ∀ {xs xs' x}
                  → xs ⊂ xs'
                  → (x ∷ xs) ⊂ (x ∷ xs')

⊂-refl : {a : Set} → (xs : List a) → xs ⊂ xs
⊂-refl [] = EmptyIsSublist
⊂-refl (x ∷ xs) = PrependBoth (⊂-refl xs)
