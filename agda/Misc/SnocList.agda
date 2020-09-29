{-# OPTIONS --safe #-}

module Misc.SnocList where

open import Data.List.Base
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality.Core

data SnocList {a : Set} : (xs : List a) → Set where
  Empty : SnocList []
  Snoc  : (x : a)
        → (xs : List a)
        → (init : SnocList xs)
        → SnocList (xs ++ [ x ])

snocList : {a : Set} → (xs : List a) → SnocList xs
snocList xs = go Empty xs
  where
    go : ∀ {xs} → SnocList xs → (ys : _) → SnocList (xs ++ ys)
    go {xs} init [] rewrite ++-identityʳ xs = init
    go {xs} init (y ∷ ys) rewrite sym (++-assoc xs [ y ] ys) = go (Snoc y xs init) ys
