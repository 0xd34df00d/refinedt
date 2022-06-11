{-# OPTIONS --safe #-}

module Intermediate.Syntax.Substitution.Commutativity where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (zero; suc)
open import Data.Fin.Base using (zero; suc; inject₁; toℕ)
open import Data.Fin.Properties using (toℕ-inject₁; suc-injective)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning

open import Data.Fin.Extra

open import Intermediate.Syntax
import Intermediate.Syntax.Renaming as R
open import Intermediate.Syntax.Substitution
open import Intermediate.Syntax.Substitution.Distributivity
open import Intermediate.Syntax.Substitution.Stable

{-
For the following two functions, it's easy to see with pen and paper that:
  if ι₂ < ι₁ then ι₁' = suc ι₁
  if ι₂ = ι₁ then ι₁' = suc ι₁
  if ι₂ > ι₁ then ι₁' = ι₁
or, equivalently,
  if ι₁ ≥ ι₂ then ι₁' = suc ι₁
  if ι₁ < ι₂ then ι₁' = ι₁
or, equivalently,
  if suc ι₁ > ι₂ then ι₁' = suc ι₁
  if suc ι₁ ≤ ι₂ then ι₁' = ι₁

Analogously:
  if ι₁ < ι₂ then ι₂' = pred ι₂
  if ι₁ = ι₂ then ι₂' = ι₂
  if ι₁ > ι₂ then ι₂' = ι₂
or, equivalently,
  if ι₁ ≥ ι₂ then ι₂' = ι₂
  if ι₁ < ι₂ then ι₂' = pred ι₂
or, equivalently,
  if suc ι₁ > ι₂ then ι₂' = ι₂
  if suc ι₁ ≤ ι₂ then ι₂' = pred ι₂
-}

compute-ι'₁ : Fin (suc ℓ) → Fin (suc (suc ℓ)) → Fin (suc (suc ℓ))
compute-ι'₁ ι₁ ι₂ with suc ι₁ <>? ι₂
... | less suc-ι₁<ι₂ = inject₁ ι₁
... | equal suc-ι₁≡ι₂ = inject₁ ι₁
... | greater suc-ι₁>ι₂ = suc ι₁

compute-ι'₂ : Fin (suc ℓ) → Fin (suc (suc ℓ)) → Fin (suc ℓ)
compute-ι'₂ ι₁ ι₂ with suc ι₁ <>? ι₂
... | less suc-ι₁<ι₂ = m<n-n-pred suc-ι₁<ι₂
... | equal suc-ι₁≡ι₂ = ι₁ -- which is the predecessor of ι₂
... | greater suc-ι₁>ι₂ = tighten suc-ι₁>ι₂

{-
if var < ι, we leave it alone
otherwise, we increment it to make room for ι
-}
make-room-for : (ι : Fin (suc ℓ))
              → (var : Fin ℓ)
              → Fin (suc ℓ)
make-room-for ι var with ι <>? inject₁ var
... | less ι<var = suc var
... | equal ι≡var = suc var
... | greater ι>var = inject₁ var

make-room-for-zero : (var : Fin ℓ)
                   → make-room-for zero var ≡ suc var
make-room-for-zero zero = refl
make-room-for-zero (suc var) = refl

private
  lemma₁ : ∀ {a : Fin ℓ} {b c : Fin (suc ℓ)}
         → (suc-a<b : suc a < b)
         → (b<c : b < c)
         → inject₁ a < c
  lemma₁ suc-a<b b<c = <-injectₗ₁ (<-weakenₗ (<-trans suc-a<b b<c))

  lemma₂ : ∀ {m : Fin ℓ} {n}
         → (suc-m<n : suc m < n)
         → m < m<n-n-pred suc-m<n
  lemma₂ {n = suc n} (<-suc m<n) = m<n

  lemma₃ : ∀ {a₁ a₂ b : Fin ℓ}
         → a₁ ≡ a₂
         → a₂ < b
         → a₁ < b
  lemma₃ refl a<b = a<b

  lemma₃-tighten-same : ∀ {a₁ a₂ b : Fin (suc ℓ)}
                      → (a₁≡a₂ : a₁ ≡ a₂)
                      → (a₂<b : a₂ < b)
                      → tighten (lemma₃ a₁≡a₂ a₂<b) ≡ tighten a₂<b
  lemma₃-tighten-same refl a<b = refl

  lemma₄ : ∀ {a : Fin ℓ} {b : Fin (suc ℓ)}
         → inject₁ a < b
         → b < suc a
         → ⊥
  lemma₄ {a = zero} _ (<-suc ())
  lemma₄ {a = suc a} {b = suc b} (<-suc a<b) (<-suc b<suc-a) = lemma₄ a<b b<suc-a

  lemma₅ : ∀ {a : Fin ℓ} {b c : Fin (suc ℓ)}
         → inject₁ a > b
         → (b<c : b < c)
         → a > tighten b<c
  lemma₅ {a = suc a} (<-zero _) (<-zero _) = <-zero a
  lemma₅ {a = suc a} (<-suc a>b) (<-suc b<c) = <-suc (lemma₅ a>b b<c)

  lemma₅-tighten-same : ∀ {ι : Fin (suc ℓ)} {var : Fin (suc (suc ℓ))}
                      → (m>n : suc ι > var)
                      → (m>n₁ : inject₁ ι > var)
                      → tighten (lemma₅ m>n₁ m>n) ≡ tighten (lemma₅ m>n₁ m>n₁)
  lemma₅-tighten-same {ι = suc ι} (<-zero _) (<-zero _) = refl
  lemma₅-tighten-same {ℓ = suc ℓ} {ι = suc ι} (<-suc m>n) (<-suc m>n₁) = cong suc (lemma₅-tighten-same m>n m>n₁)

  lemma₆ : ∀ {a c : Fin (suc ℓ)} {b : Fin ℓ}
         → a < b
         → (a<c : a < c)
         → tighten a<c < b
  lemma₆ {ℓ = suc ℓ} (<-zero _) (<-zero _) = <-zero _
  lemma₆ {ℓ = suc ℓ} (<-suc a<b) (<-suc a<c) = <-suc (lemma₆ a<b a<c)

  lemma₇ : ∀ {a : Fin ℓ} {b c : Fin (suc ℓ)}
         → inject₁ a < b
         → (b<c : b < c)
         → a < tighten b<c
  lemma₇ {a = zero} (<-zero _) (<-suc _) = <-zero _
  lemma₇ {a = suc a} (<-suc a<b) (<-suc b<c) = <-suc (lemma₇ a<b b<c)

  lemma₈ : ∀ {a : Fin ℓ} {b c : Fin (suc ℓ)}
         → inject₁ a > b
         → (b<c : b < c)
         → a > tighten b<c
  lemma₈ {a = suc a} {b = zero} (<-zero _) (<-zero _) = <-zero _
  lemma₈ {a = suc a} {b = suc b} (<-suc a>b) (<-suc b<c) = <-suc (lemma₈ a>b b<c)

  lemma₉ : ∀ {var : Fin (suc ℓ)} {a b : Fin ℓ}
         → (var<a : var < inject₁ a)
         → suc a < suc b
         → tighten var<a < b
  lemma₉ {a = a} var<a (<-suc a<b) = <-trans (</toℕ (tighten-preserves-<ₗ var<a) refl (sym (toℕ-inject₁ a))) a<b

  lemma₁₀ : ∀ {a : Fin ℓ} {b c : Fin (suc ℓ)}
          → inject₁ a ≡ b
          → (b<c : b < c)
          → a ≡ tighten b<c
  lemma₁₀ {suc ℓ} {a = zero} _ (<-zero n) = refl
  lemma₁₀ {suc ℓ} {a = suc a} ≡-prf (<-suc b<c) = cong suc (lemma₁₀ (suc-injective ≡-prf) b<c)

  subst-make-room-id-var : (ι : Fin (suc ℓ))
                         → (ε' ε : ITerm ℓ)
                         → ∀ var → replace-at ι ε' (make-room-for ι var) ≡ IVar var
  subst-make-room-id-var ι ε' ε var with ι <>? inject₁ var
  ... | less ι<var rewrite <>?-< (<-trans ι<var (inject₁-n<suc-n var)) = refl
  ... | equal refl rewrite <>?-< (inject₁-n<suc-n var) = refl
  ... | greater ι>var rewrite <>?-> ι>var
                              | lift-ℕ-≡
                                (
                                begin
                                  toℕ (tighten ι>var)
                                ≡⟨ tighten-is-same-ℕ ι>var ⟩
                                  toℕ (inject₁ var)
                                ≡⟨ toℕ-inject₁ var ⟩
                                  toℕ var
                                ∎
                                )
                              = refl

  subst-make-room-id-ε : (ι : Fin (suc ℓ))
                       → (ε' ε : ITerm ℓ)
                       → [ ι ↦ε ε' ] R.act-ε (make-room-for ι) ε ≡ ε
  subst-make-room-id-ε ι ε' ε
    rewrite σ-ρ-distr-ε (replace-at ι ε') (make-room-for ι) ε
          = act-ε-id (subst-make-room-id-var ι ε' ε) ε

subst-commutes-var : (ε₁ : ITerm ℓ)
                   → (ε₂ : ITerm (suc ℓ))
                   → (ι₁ : Fin (suc ℓ))
                   → (ι₂ : Fin (suc (suc ℓ)))
                   → (var : Fin (suc (suc ℓ)))
                   → (let ι'₁ = compute-ι'₁ ι₁ ι₂)
                   → (let ι'₂ = compute-ι'₂ ι₁ ι₂)
                   → [ ι₁ ↦ε ε₁ ] [ ι₂ ↦ε ε₂ ] (IVar var) ≡ [ ι'₂ ↦ε [ ι₁ ↦ε ε₁ ] ε₂ ] [ ι'₁ ↦ε R.act-ε (make-room-for ι'₂) ε₁ ] (IVar var)
subst-commutes-var ε₁ ε₂ ι₁ ι₂ var with suc ι₁ <>? ι₂ | ι₂ <>? var
... | less m<n@(<-suc m<n') | less m<n₁@(<-suc m<n₁')
  rewrite <>?-< (lemma₁ m<n m<n₁)
        | <>?-< (<-trans m<n' m<n₁')
        | <>?-< m<n₁'
        | pred-always-same (<-trans m<n' m<n₁') m<n₁'
        = refl
... | less m<n | equal refl
  rewrite <>?-< (<-injectₗ₁ (<-weakenₗ m<n))
        | <>?-≡ (pred-always-same m<n (<-injectₗ₁ (<-weakenₗ m<n)))
        = refl
... | equal refl | less m<n
  rewrite <>?-< (<-injectₗ₁ (<-weakenₗ m<n))
        | pred-always-same (<-injectₗ₁ (<-weakenₗ m<n)) m<n
        | <>?-< (lemma₂ m<n)
        = refl
... | equal refl | equal refl
  rewrite <>?-< (<-injectₗ₁ (n<suc-n ι₁))
        | <>?-refl-equal ι₁
        = refl
... | greater m>n | equal refl
  rewrite <>?-> m>n
        | <>?-refl-equal (tighten m>n)
        = refl
... | greater m>n | greater m>n₁
  rewrite <>?-> (>-trans m>n m>n₁)
        | tighten-same (>-trans m>n m>n₁) m>n₁
        | <>?-> (tighten-preserves-< m>n₁ m>n)
        | <>?-> (lemma₃ (tighten-same m>n₁ (<-injectᵣ₁ (a<b≤c m>n₁ m>n))) (<-unjectᵣ₁ (tighten-preserves-<ₗ (<-injectᵣ₁ (a<b≤c m>n₁ m>n)))))
        | lemma₃-tighten-same (tighten-same m>n₁ (<-injectᵣ₁ (a<b≤c m>n₁ m>n))) (<-unjectᵣ₁ (tighten-preserves-<ₗ (<-injectᵣ₁ (a<b≤c m>n₁ m>n))))
        | lift-ℕ-≡
          (
          begin
            toℕ (tighten (<-unjectᵣ₁ (tighten-preserves-<ₗ (<-injectᵣ₁ (a<b≤c m>n₁ m>n)))))
          ≡⟨ tighten-is-same-ℕ (<-unjectᵣ₁ (tighten-preserves-<ₗ (<-injectᵣ₁ (a<b≤c m>n₁ m>n)))) ⟩
            toℕ (tighten (<-injectᵣ₁ (a<b≤c m>n₁ m>n)))
          ≡⟨ tighten-is-same-ℕ (<-injectᵣ₁ (a<b≤c m>n₁ m>n)) ⟩
            toℕ var
          ≡˘⟨ tighten-is-same-ℕ m>n₁ ⟩
            toℕ (tighten m>n₁)
          ≡˘⟨ tighten-is-same-ℕ (tighten-preserves-< m>n₁ m>n) ⟩
            toℕ (tighten (tighten-preserves-< m>n₁ m>n))
          ∎
          )
        = refl
subst-commutes-var ε₁ ε₂ ι₁ ι₂ var | equal refl | greater m>n with inject₁ ι₁ <>? var
...   | less m<n = ⊥-elim (lemma₄ m<n m>n)
...   | equal m≡n rewrite <>?-≡ (lemma₁₀ m≡n m>n) = sym (subst-make-room-id-ε ι₁ _ ε₁)
...   | greater m>n₁ rewrite <>?-> (lemma₅ m>n₁ m>n)
                           | <>?-> (lemma₅ m>n₁ m>n₁)
                           | lemma₅-tighten-same m>n m>n₁
                           = refl
subst-commutes-var ε₁ ε₂ ι₁ ι₂ (suc var) | greater m>n | less m<n with ι₁ <>? var
...   | less m<n₁ rewrite <>?-< (lemma₆ (a≤b<c m>n m<n₁) m>n)
                        | pred-always-same (lemma₆ (a≤b<c m>n m<n₁) m>n) m<n₁
                        = refl
...   | equal refl = sym (subst-make-room-id-ε (tighten m>n) _ ε₁)
...   | greater m>n₁ rewrite <>?-< (</toℕ m<n (tighten-is-same-ℕ m>n) (cong suc (tighten-is-same-ℕ m>n₁))) = refl
subst-commutes-var ε₁ ε₂ ι₁ (suc ι₂) var | less m<n | greater m>n with inject₁ ι₁ <>? var
...   | equal m≡n rewrite <>?-≡ (lemma₁₀ m≡n m>n) = sym (subst-make-room-id-ε ι₂ _ ε₁)
...   | greater m>n₁ rewrite <>?-> (lemma₈ m>n₁ m>n)
                           | <>?-> (lemma₉ m>n₁ m<n)
                           | lift-ℕ-≡
                             (
                             begin
                               toℕ (tighten (lemma₈ m>n₁ m>n))
                             ≡⟨ tighten-is-same-ℕ (lemma₈ m>n₁ m>n) ⟩
                               toℕ (tighten m>n)
                             ≡⟨ cong toℕ (tighten-same m>n m>n₁) ⟩
                               toℕ (tighten m>n₁)
                             ≡˘⟨ tighten-is-same-ℕ (lemma₉ m>n₁ m<n) ⟩
                               toℕ (tighten (lemma₉ m>n₁ m<n))
                             ∎
                             )
                           = refl
...   | less m<n₁ rewrite <>?-< (lemma₇ m<n₁ m>n) with var | m>n
...                                                  | suc var' | <-suc m>n' rewrite <>?-> m>n' = refl

subst-commutes-τ : ∀ ι₁ ι₂ ε₁ ε₂ (τ : IType (suc (suc ℓ)))
                 → (let ι'₁ = compute-ι'₁ ι₁ ι₂)
                 → (let ι'₂ = compute-ι'₂ ι₁ ι₂)
                 → [ ι₁ ↦τ ε₁ ] [ ι₂ ↦τ ε₂ ] τ ≡ [ ι'₂ ↦τ [ ι₁ ↦ε ε₁ ] ε₂ ] [ ι'₁ ↦τ R.act-ε (make-room-for ι'₂) ε₁ ] τ
subst-commutes-τ ι₁ ι₂ ε₁ ε₂ τ rewrite act-τ-distr (replace-at ι₂ ε₂) (replace-at ι₁ ε₁) τ
                                     | act-τ-distr
                                           (replace-at (compute-ι'₁ ι₁ ι₂) (R.act-ε (make-room-for (compute-ι'₂ ι₁ ι₂)) ε₁))
                                           (replace-at (compute-ι'₂ ι₁ ι₂) ([ ι₁ ↦ε ε₁ ] ε₂)) τ
                                     | act-τ-extensionality (subst-commutes-var ε₁ ε₂ ι₁ ι₂) τ
                                     = refl

subst-commutes-ε : ∀ ι₁ ι₂ ε₁ ε₂ (ε : ITerm (suc (suc ℓ)))
                 → (let ι'₁ = compute-ι'₁ ι₁ ι₂)
                 → (let ι'₂ = compute-ι'₂ ι₁ ι₂)
                 → [ ι₁ ↦ε ε₁ ] [ ι₂ ↦ε ε₂ ] ε ≡ [ ι'₂ ↦ε [ ι₁ ↦ε ε₁ ] ε₂ ] [ ι'₁ ↦ε R.act-ε (make-room-for ι'₂) ε₁ ] ε
subst-commutes-ε ι₁ ι₂ ε₁ ε₂ ε rewrite act-ε-distr (replace-at ι₂ ε₂) (replace-at ι₁ ε₁) ε
                                     | act-ε-distr
                                           (replace-at (compute-ι'₁ ι₁ ι₂) (R.act-ε (make-room-for (compute-ι'₂ ι₁ ι₂)) ε₁))
                                           (replace-at (compute-ι'₂ ι₁ ι₂) ([ ι₁ ↦ε ε₁ ] ε₂)) ε
                                     | act-ε-extensionality (subst-commutes-var ε₁ ε₂ ι₁ ι₂) ε
                                     = refl

subst-commutes-τ-zero : ∀ ι ε₁ ε₂ (τ : IType (suc (suc ℓ)))
                      → [ ι ↦τ ε₁ ] [ zero ↦τ ε₂ ] τ ≡ [ zero ↦τ [ ι ↦ε ε₁ ] ε₂ ] [ suc ι ↦τ R.weaken-ε ε₁ ] τ
subst-commutes-τ-zero ι ε₁ ε₂ τ rewrite R.act-ε-extensionality (sym ∘ make-room-for-zero) ε₁ = subst-commutes-τ ι zero ε₁ ε₂ τ

subst-commutes-ε-zero : ∀ ι ε₁ ε₂ (ε : ITerm (suc (suc ℓ)))
                      → [ ι ↦ε ε₁ ] [ zero ↦ε ε₂ ] ε ≡ [ zero ↦ε [ ι ↦ε ε₁ ] ε₂ ] [ suc ι ↦ε R.weaken-ε ε₁ ] ε
subst-commutes-ε-zero ι ε₁ ε₂ ε rewrite R.act-ε-extensionality (sym ∘ make-room-for-zero) ε₁ = subst-commutes-ε ι zero ε₁ ε₂ ε
