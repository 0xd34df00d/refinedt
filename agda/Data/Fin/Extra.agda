{-# OPTIONS --safe #-}

module Data.Fin.Extra where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using () renaming (suc-injective to ℕ-suc-injective)
open import Data.Fin using (Fin; zero; suc; toℕ; inject₁)
open import Data.Fin.Properties using (suc-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)

private
  variable
    ℓ ℓ' ℓ₁ ℓ₂ ℓ₃ : ℕ
    m n : Fin ℓ

data _<_ : Fin ℓ → Fin ℓ' → Set where
  <-zero : (n : Fin ℓ')
         → zero {n = ℓ} < suc n
  <-suc  : m < n
         → suc m < suc n

<-suc-injective : {m<n m<n' : m < n}
                → <-suc m<n ≡ <-suc m<n'
                → m<n ≡ m<n'
<-suc-injective refl = refl

m<n-not-equal : m < n → ¬ m ≡ n
m<n-not-equal (<-zero n) = λ ()
m<n-not-equal (<-suc m<n) = λ suc-m≡suc-n → m<n-not-equal m<n (suc-injective suc-m≡suc-n)

n<suc-n : (n : Fin ℓ) → n < suc n
n<suc-n zero = <-zero zero
n<suc-n (suc n) = <-suc (n<suc-n n)

<-antireflexive : ∀ {m : Fin ℓ} → ¬ m < m
<-antireflexive (<-suc m<m) = <-antireflexive m<m

<-trans : {a b c : Fin ℓ}
        → a < b
        → b < c
        → a < c
<-trans (<-zero n) (<-suc b<c) = <-zero _
<-trans (<-suc a<b) (<-suc b<c) = <-suc (<-trans a<b b<c)

m<n⇒0<n : m < n → zero {ℓ} < n
m<n⇒0<n {n = suc n} _ = <-zero n

¬n<0 : {n : Fin ℓ} → ¬ n < zero {ℓ'}
¬n<0 ()

a≤b<c : {a b c : Fin ℓ}
      → (a < suc b)
      → (b < c)
      → a < c
a≤b<c (<-zero zero) (<-zero _) = <-zero _
a≤b<c (<-zero (suc b)) (<-suc _) = <-zero _
a≤b<c (<-suc a≤b) (<-suc b<c) = <-suc (a≤b<c a≤b b<c)

a<b<c : ∀ {a : Fin ℓ₁} {b : Fin ℓ₂} {c : Fin ℓ₃}
      → a < b
      → b < c
      → suc a < c
a<b<c (<-zero n) (<-suc b<c) = <-suc (m<n⇒0<n b<c)
a<b<c (<-suc a<b) (<-suc b<c) = <-suc (a<b<c a<b b<c)

a<b≤c : ∀ {a : Fin ℓ₁} {b : Fin ℓ₂} {c : Fin ℓ₃}
      → (a < b)
      → (b < suc c)
      → a < c
a<b≤c (<-zero n) (<-suc b≤c) = m<n⇒0<n b≤c
a<b≤c (<-suc a<b) (<-suc b<c) = a<b<c a<b b<c

<-injectₗ₁ : m < n
           → inject₁ m < n
<-injectₗ₁ (<-zero n) = <-zero n
<-injectₗ₁ (<-suc m<n) = <-suc (<-injectₗ₁ m<n)

<-injectᵣ₁ : m < n
           → m < inject₁ n
<-injectᵣ₁ (<-zero n) = <-zero (inject₁ n)
<-injectᵣ₁ (<-suc m<n) = <-suc (<-injectᵣ₁ m<n)

<-unjectᵣ₁ : m < inject₁ n
           → m < n
<-unjectᵣ₁ m<n = helper m<n refl
  where
    helper : ∀ {n'}
           → m < n'
           → n' ≡ inject₁ n
           → m < n
    helper {n = suc n} (<-zero _) _ = <-zero n
    helper {n = suc n} (<-suc m<n') refl = <-suc (helper m<n' refl)

<-weakenₗ : suc m < n
          → m < n
<-weakenₗ {m = zero} (<-suc suc-m<n) = <-zero _
<-weakenₗ {m = suc m} (<-suc suc-m<n) = <-suc (<-weakenₗ suc-m<n)

<-weakenᵣ : m < n
          → m < suc n
<-weakenᵣ (<-zero n) = <-zero (suc n)
<-weakenᵣ (<-suc m<n) = <-suc (<-weakenᵣ m<n)

_>_ : Fin ℓ → Fin ℓ' → Set
m > n = n < m

>-trans : {a b c : Fin ℓ}
        → a > b
        → b > c
        → a > c
>-trans a>b b>c = <-trans b>c a>b


m<n-not-m>n : m < n → ¬ m > n
m<n-not-m>n (<-zero n) ()
m<n-not-m>n (<-suc m<n) (<-suc m>n) = m<n-not-m>n m<n m>n

m<n-not-m≡n : m < n → ¬ m ≡ n
m<n-not-m≡n (<-suc m<n) refl = m<n-not-m≡n m<n refl

m<n-n-pred : {m n : Fin (suc ℓ)} → m < n → Fin ℓ
m<n-n-pred {n = suc n} _ = n

m<n-n-pred-cancel : ∀ {m n : Fin (suc ℓ)} → (m<n : m < n) → suc (m<n-n-pred m<n) ≡ n
m<n-n-pred-cancel {n = suc n} m<n = refl

m<n⇒n<suc-pred-n : ∀ {m n : Fin (suc ℓ)} → (m<n : m < n) → m < suc (m<n-n-pred m<n)
m<n⇒n<suc-pred-n m<n rewrite m<n-n-pred-cancel m<n = m<n

pred-always-same : ∀ {m₁ m₂ n : Fin (suc ℓ)}
                 → (m₁<n : m₁ < n)
                 → (m₂<n : m₂ < n)
                 → m<n-n-pred m₁<n ≡ m<n-n-pred m₂<n
pred-always-same {n = suc n} _ _ = refl

tighten : ∀ {m n : Fin (suc ℓ)} → m < n → Fin ℓ
tighten {suc ℓ} (<-zero _) = zero
tighten {suc ℓ} (<-suc m<n) = suc (tighten m<n)

tighten-is-same-ℕ : ∀ {m n : Fin (suc ℓ)} → (m<n : m < n) → toℕ (tighten m<n) ≡ toℕ m
tighten-is-same-ℕ {suc ℓ} (<-zero _) = refl
tighten-is-same-ℕ {suc ℓ} (<-suc m<n) rewrite tighten-is-same-ℕ m<n = refl

tighten-zero : ∀ (n : Fin (suc ℓ)) → tighten (<-zero n) ≡ zero
tighten-zero _ = refl

tighten-preserves-<ₗ : (m<n : m < n)
                     → tighten m<n < n
tighten-preserves-<ₗ {suc ℓ} (<-zero n) = <-zero n
tighten-preserves-<ₗ {suc ℓ} (<-suc m<n) = <-suc (tighten-preserves-<ₗ m<n)

tighten-preserves-<ᵣ : {a b c : Fin (suc ℓ)}
                     → (a<b : a < b)
                     → (b<c : b < c)
                     → a < tighten b<c
tighten-preserves-<ᵣ {suc ℓ} (<-zero _) (<-suc b<c) = <-zero (tighten b<c)
tighten-preserves-<ᵣ {suc ℓ} (<-suc a<b) (<-suc b<c) = <-suc (tighten-preserves-<ᵣ a<b b<c)

tighten-preserves-< : {a b c : Fin (suc ℓ)}
                    → (a<b : a < b)
                    → (b<c : b < c)
                    → tighten a<b < tighten b<c
tighten-preserves-< {suc ℓ} (<-zero n) (<-suc b<c) = <-zero (tighten b<c)
tighten-preserves-< {suc ℓ} (<-suc a<b) (<-suc b<c) = <-suc (tighten-preserves-< a<b b<c)

tighten-preserves-<-toℕ : {a b c : Fin (suc (suc ℓ))}
                        → (a<b : a < b)
                        → (b<c : b < c)
                        → toℕ (tighten (tighten-preserves-< a<b b<c)) ≡ toℕ a
tighten-preserves-<-toℕ {ℓ = zero} {c = suc zero} (<-zero zero) (<-suc ())
tighten-preserves-<-toℕ {ℓ = suc ℓ} (<-zero n) (<-suc b<c) = refl
tighten-preserves-<-toℕ {ℓ = suc ℓ} (<-suc a<b) (<-suc b<c) = cong suc (tighten-preserves-<-toℕ a<b b<c)

suc-tighten : ∀ {m n : Fin (suc ℓ)} → (m<n : m < n) → suc (tighten m<n) < suc n
suc-tighten {ℓ = suc ℓ} (<-zero n) = <-suc (<-zero n)
suc-tighten {ℓ = suc ℓ} (<-suc m<n) = <-suc (suc-tighten m<n)

tighten-same : ∀ {m n₁ n₂ : Fin (suc ℓ)}
             → (m<n₁ : m < n₁)
             → (m<n₂ : m < n₂)
             → tighten m<n₁ ≡ tighten m<n₂
tighten-same {suc ℓ} (<-zero n₁) (<-zero n₂) = refl
tighten-same {suc ℓ} (<-suc m<n₁) (<-suc m<n₂) = cong suc (tighten-same m<n₁ m<n₂)


data _<>_ : Fin ℓ → Fin ℓ → Set where
  less    : (m<n : m < n) → m <> n
  equal   : (m≡n : m ≡ n) → m <> n
  greater : (m>n : m > n) → m <> n

less-injective : ∀ {m<n m<n' : m < n}
               → less m<n ≡ less m<n'
               → m<n ≡ m<n'
less-injective refl = refl

¬equal≡less : {m≡n : m ≡ n}
            → {m<n : m < n}
            → ¬ equal (m≡n) ≡ less (m<n)
¬equal≡less ()


_<>?_ : (m n : Fin ℓ) → m <> n
zero <>? zero = equal refl
zero <>? suc n = less (<-zero n)
suc m <>? zero = greater (<-zero m)
suc m <>? suc n with m <>? n
... | less m<n = less (<-suc m<n)
... | equal refl = equal refl
... | greater m>n = greater (<-suc m>n)

<>?-refl-equal : ∀ (n : Fin ℓ) → n <>? n ≡ equal refl
<>?-refl-equal zero = refl
<>?-refl-equal (suc n) rewrite <>?-refl-equal n = refl

<>?-≡ : (m≡n : m ≡ n) → m <>? n ≡ equal m≡n
<>?-≡ refl = <>?-refl-equal _

<>?-< : (m<n : m < n) → m <>? n ≡ less m<n
<>?-< (<-zero n) = refl
<>?-< (<-suc m<n) rewrite <>?-< m<n = refl

<>?-> : (m>n : m > n) → m <>? n ≡ greater m>n
<>?-> (<-zero n) = refl
<>?-> (<-suc m>n) rewrite <>?-> m>n = refl

<>?-<-suc : (m<n : m < n)
          → suc m <>? suc n ≡ less (<-suc m<n)
          → m <>? n ≡ less m<n
<>?-<-suc {m = m} {n = n} m<n ≡-prf with m <>? n
... | less m<n' rewrite <-suc-injective (less-injective ≡-prf) = refl
... | equal refl = ⊥-elim (¬equal≡less ≡-prf)


Monotonic : (f : Fin ℓ → Fin ℓ') → Set
Monotonic f = ∀ {x y} → x < y → f x < f y

Fin0-elim : {A : Set} → Fin zero → A
Fin0-elim ()

lift-ℕ-≡ : toℕ m ≡ toℕ n → m ≡ n
lift-ℕ-≡ {m = zero} {n = zero} ℕ-≡ = refl
lift-ℕ-≡ {m = suc m} {n = suc n} ℕ-≡ rewrite lift-ℕ-≡ (ℕ-suc-injective ℕ-≡) = refl

tighten-injective : {m₁ m₂ n : Fin (suc ℓ)}
                  → {m₁<n : m₁ < n}
                  → {m₂<n : m₂ < n}
                  → tighten m₁<n ≡ tighten m₂<n
                  → m₁ ≡ m₂
tighten-injective {m₁<n = m₁<n} {m₂<n = m₂<n} ≡-prf with cong toℕ ≡-prf
... | cong-prf rewrite tighten-is-same-ℕ m₁<n
                     | tighten-is-same-ℕ m₂<n
                     = lift-ℕ-≡ cong-prf

m<n-n-pred-injective : {m₁ m₂ n : Fin (suc ℓ)}
                     → {n<m₁ : n < m₁}
                     → {n<m₂ : n < m₂}
                     → m<n-n-pred n<m₁ ≡ m<n-n-pred n<m₂
                     → m₁ ≡ m₂
m<n-n-pred-injective {n<m₁ = n<m₁} {n<m₂ = n<m₂} ≡-prf with cong Fin.suc ≡-prf
... | cong-prf rewrite m<n-n-pred-cancel n<m₁
                     | m<n-n-pred-cancel n<m₂
                     = cong-prf
