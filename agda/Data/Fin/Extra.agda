{-# OPTIONS --safe #-}

module Data.Fin.Extra where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    ℓ : ℕ
    m n : Fin ℓ

data _<_ : Fin ℓ → Fin ℓ → Set where
  <-zero : ∀ {ℓ} (n : Fin ℓ)
         → zero < suc n
  <-suc  : ∀ {ℓ} {m n : Fin ℓ}
         → m < n
         → suc m < suc n

_>_ : Fin ℓ → Fin ℓ → Set
m > n = n < m

data _<>_ : Fin ℓ → Fin ℓ → Set where
  less    : (m<n : m < n) → m <> n
  equal   :                 m <> m
  greater : (m>n : m > n) → m <> n

_<>?_ : (m n : Fin ℓ) → m <> n
zero <>? zero = equal
zero <>? suc n = less (<-zero n)
suc m <>? zero = greater (<-zero m)
suc m <>? suc n with m <>? n
... | less m<n = less (<-suc m<n)
... | equal = equal
... | greater m>n = greater (<-suc m>n)
