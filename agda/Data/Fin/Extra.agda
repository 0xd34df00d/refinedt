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

m<n-n-pred : {m n : Fin (suc ℓ)} → m < n → Fin ℓ
m<n-n-pred {n = suc n} _ = n

m<n-n-pred-cancel : ∀ {m n : Fin (suc ℓ)} → (m<n : m < n) → suc (m<n-n-pred m<n) ≡ n
m<n-n-pred-cancel {n = suc n} m<n = refl

tighten : ∀ {m n : Fin (suc ℓ)} → m > n → Fin ℓ
tighten (<-zero zero) = zero
tighten (<-zero (suc m)) = zero
tighten {ℓ = suc ℓ} (<-suc m>n) = suc (tighten m>n)

tighten-is-same-ℕ : ∀ {m n : Fin (suc ℓ)} → (m>n : m > n) → toℕ (tighten m>n) ≡ toℕ n
tighten-is-same-ℕ (<-zero zero) = refl
tighten-is-same-ℕ (<-zero (suc n)) = refl
tighten-is-same-ℕ {ℓ = suc ℓ} (<-suc m>n) rewrite tighten-is-same-ℕ m>n = refl
