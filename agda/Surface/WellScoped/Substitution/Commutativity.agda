{-# OPTIONS --safe #-}

module Surface.WellScoped.Substitution.Commutativity where

open import Data.Nat.Base using (zero; suc)
open import Data.Fin.Base using (zero; suc; inject₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Fin.Extra
open import Surface.WellScoped
import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.Substitution
open import Surface.WellScoped.Substitution.Distributivity
open import Surface.WellScoped.Substitution.Stable

{-
subst-commutes-var : ∀ ε (ε₂ : STerm (suc ℓ)) ι
                   → ∀ var → [ ι ↦ε ε ] [ zero ↦ε ε₂ ] (SVar var) ≡ [ zero ↦ε [ ι ↦ε ε ] ε₂ ] [ suc ι ↦ε R.weaken-ε ε ] (SVar var)
subst-commutes-var ε ε₂ zero zero = refl
subst-commutes-var ε ε₂ zero (suc var) with zero <>? var
... | less m<n rewrite <>?-< m<n = refl
... | equal refl rewrite replace-weakened-ε zero ([ zero ↦ε ε ] ε₂) ε
                       | R.act-ε-id (λ _ → refl) ε = refl
subst-commutes-var ε ε₂ (suc ι) zero = refl
subst-commutes-var ε ε₂ (suc ι) (suc var) with suc ι <>? var
... | less m<n rewrite <>?-< (m<n⇒0<n m<n)
                     | pred-always-same m<n (m<n⇒0<n m<n) = refl
... | equal refl rewrite replace-weakened-ε zero ([ suc ι ↦ε ε ] ε₂) ε
                       | R.act-ε-id (λ _ → refl) ε = refl
... | greater m>n = refl

subst-commutes-τ : ∀ ι ε ε₂ (τ : SType (suc (suc ℓ)))
                 → [ ι ↦τ ε ] [ zero ↦τ ε₂ ] τ ≡ [ zero ↦τ [ ι ↦ε ε ] ε₂ ] [ suc ι ↦τ R.weaken-ε ε ] τ
subst-commutes-τ ι ε ε₂ τ rewrite act-τ-distr (replace-at zero ε₂) (replace-at ι ε) τ
                                | act-τ-distr (replace-at (suc ι) (R.weaken-ε ε)) (replace-at zero ([ ι ↦ε ε ] ε₂)) τ
                                | act-τ-extensionality (subst-commutes-var ε ε₂ ι) τ
                                = refl

subst-commutes-ε : ∀ ι ε ε₂ (ε₀ : STerm (suc (suc ℓ)))
                 → [ ι ↦ε ε ] [ zero ↦ε ε₂ ] ε₀ ≡ [ zero ↦ε [ ι ↦ε ε ] ε₂ ] [ suc ι ↦ε R.weaken-ε ε ] ε₀
subst-commutes-ε ι ε ε₂ ε₀ rewrite act-ε-distr (replace-at zero ε₂) (replace-at ι ε) ε₀
                                 | act-ε-distr (replace-at (suc ι) (R.weaken-ε ε)) (replace-at zero ([ ι ↦ε ε ] ε₂)) ε₀
                                 | act-ε-extensionality (subst-commutes-var ε ε₂ ι) ε₀
                                 = refl
                                 -}

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
if var < ι₂ (or, equivalently, suc var ≤ ι₂), we leave it alone
otherwise, we increment it to make room for ι₂
-}
make-room-for : (ι : Fin (suc ℓ))
              → (var : Fin ℓ)
              → Fin (suc ℓ)
make-room-for ι var with ι <>? suc var
... | less m<n = inject₁ var
... | equal m≡n = inject₁ var
... | greater m>n = suc var

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

subst-commutes-var : (ε₁ : STerm ℓ)
                   → (ε₂ : STerm (suc ℓ))
                   → (ι₁ : Fin (suc ℓ))
                   → (ι₂ : Fin (suc (suc ℓ)))
                   → (var : Fin (suc (suc ℓ)))
                   → (let ι'₁ = compute-ι'₁ ι₁ ι₂)
                   → (let ι'₂ = compute-ι'₂ ι₁ ι₂)
                   → [ ι₁ ↦ε ε₁ ] [ ι₂ ↦ε ε₂ ] (SVar var) ≡ [ ι'₂ ↦ε [ ι₁ ↦ε ε₁ ] ε₂ ] [ ι'₁ ↦ε R.act-ε (make-room-for ι'₂) ε₁ ] (SVar var)
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
... | equal refl | equal refl = {! !}
... | equal refl | greater m>n = {! !}
... | greater m>n | equal refl = {! !}
... | greater m>n | greater m>n₁ = {! !}

... | greater m>n | less m<n = {! !}
... | less m<n | greater m>n = {! !}

subst-commutes-τ : ∀ ι₁ ι₂ ε₁ ε₂ (τ : SType (suc (suc ℓ)))
                 → (let ι'₁ = compute-ι'₁ ι₁ ι₂)
                 → (let ι'₂ = compute-ι'₂ ι₁ ι₂)
                 → [ ι₁ ↦τ ε₁ ] [ ι₂ ↦τ ε₂ ] τ ≡ [ ι'₂ ↦τ [ ι₁ ↦ε ε₁ ] ε₂ ] [ ι'₁ ↦τ R.act-ε (make-room-for ι'₂) ε₁ ] τ
subst-commutes-τ ι₁ ι₂ ε₁ ε₂ τ rewrite act-τ-distr (replace-at ι₂ ε₂) (replace-at ι₁ ε₁) τ
                                     | act-τ-distr
                                           (replace-at (compute-ι'₁ ι₁ ι₂) (R.act-ε (make-room-for (compute-ι'₂ ι₁ ι₂)) ε₁))
                                           (replace-at (compute-ι'₂ ι₁ ι₂) ([ ι₁ ↦ε ε₁ ] ε₂)) τ
                                     | act-τ-extensionality (subst-commutes-var ε₁ ε₂ ι₁ ι₂) τ
                                     = refl
