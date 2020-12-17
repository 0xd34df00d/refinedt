{-# OPTIONS --safe #-}

module Data.Fin.Extra where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties renaming (suc-injective to ℕ-suc-injective)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Fin.Properties using (suc-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

private
  variable
    ℓ ℓ' : ℕ
    m n : Fin ℓ

data _<_ : Fin ℓ → Fin ℓ' → Set where
  <-zero : (n : Fin ℓ')
         → zero {n = ℓ} < suc n
  <-suc  : m < n
         → suc m < suc n

m<n-not-equal : m < n → ¬ m ≡ n
m<n-not-equal (<-zero n) = λ ()
m<n-not-equal (<-suc m<n) = λ suc-m≡suc-n → m<n-not-equal m<n (suc-injective suc-m≡suc-n)

m<n⇒0<n : m < n → zero {n = ℓ} < n
m<n⇒0<n {n = suc n} _ = <-zero n

<-weaken : m < n → m < suc n
<-weaken (<-zero n) = <-zero (suc n)
<-weaken (<-suc m<n) = <-suc (<-weaken m<n)

_>_ : Fin ℓ → Fin ℓ' → Set
m > n = n < m

m<n-not-m>n : m < n → ¬ m > n
m<n-not-m>n (<-zero n) ()
m<n-not-m>n (<-suc m<n) (<-suc m>n) = m<n-not-m>n m<n m>n

m<n-n-pred : {m n : Fin (suc ℓ)} → m < n → Fin ℓ
m<n-n-pred {n = suc n} _ = n

m<n-n-pred-cancel : ∀ {m n : Fin (suc ℓ)} → (m<n : m < n) → suc (m<n-n-pred m<n) ≡ n
m<n-n-pred-cancel {n = suc n} m<n = refl

data _<>_ : Fin ℓ → Fin ℓ → Set where
  less    : (m<n : m < n) → m <> n
  equal   : (m≡n : m ≡ n) → m <> n
  greater : (m>n : m > n) → m <> n

_<>?_ : (m n : Fin ℓ) → m <> n
zero <>? zero = equal refl
zero <>? suc n = less (<-zero n)
suc m <>? zero = greater (<-zero m)
suc m <>? suc n with m <>? n
... | less m<n = less (<-suc m<n)
... | equal refl = equal refl
... | greater m>n = greater (<-suc m>n)

tighten : ∀ {m n : Fin (suc ℓ)} → m > n → Fin ℓ
tighten (<-zero zero) = zero
tighten (<-zero (suc m)) = zero
tighten {ℓ = suc ℓ} (<-suc m>n) = suc (tighten m>n)

tighten-is-same-ℕ : ∀ {m n : Fin (suc ℓ)} → (m>n : m > n) → toℕ (tighten m>n) ≡ toℕ n
tighten-is-same-ℕ (<-zero zero) = refl
tighten-is-same-ℕ (<-zero (suc n)) = refl
tighten-is-same-ℕ {ℓ = suc ℓ} (<-suc m>n) rewrite tighten-is-same-ℕ m>n = refl

tighten-zero : ∀ (n : Fin (suc ℓ)) → tighten (<-zero n) ≡ zero
tighten-zero zero = refl
tighten-zero (suc n) = refl

tighten-preserves-< : (n>m : n > m) → tighten n>m < n
tighten-preserves-< (<-zero zero) = <-zero zero
tighten-preserves-< (<-zero (suc n)) = <-zero (suc n)
tighten-preserves-< {ℓ = suc ℓ} (<-suc n>m) = <-suc (tighten-preserves-< n>m)

<>?-refl-equal : ∀ (n : Fin ℓ) → n <>? n ≡ equal refl
<>?-refl-equal zero = refl
<>?-refl-equal (suc n) rewrite <>?-refl-equal n = refl

<>?-< : (m<n : m < n) → m <>? n ≡ less m<n
<>?-< (<-zero n) = refl
<>?-< (<-suc m<n) rewrite <>?-< m<n = refl

<>?-> : (m>n : m > n) → m <>? n ≡ greater m>n
<>?-> (<-zero n) = refl
<>?-> (<-suc m>n) rewrite <>?-> m>n = refl

Monotonic : (f : Fin ℓ → Fin ℓ') → Set
Monotonic f = ∀ {x y} → x < y → f x < f y

Fin0-elim : {A : Set} → Fin zero → A
Fin0-elim ()

lift-ℕ-≡ : toℕ m ≡ toℕ n → m ≡ n
lift-ℕ-≡ {m = zero} {n = zero} ℕ-≡ = refl
lift-ℕ-≡ {m = suc m} {n = suc n} ℕ-≡ rewrite lift-ℕ-≡ (ℕ-suc-injective ℕ-≡) = refl
