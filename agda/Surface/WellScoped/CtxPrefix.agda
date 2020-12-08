{-# OPTIONS --safe #-}

module Surface.WellScoped.CtxPrefix where

open import Data.Nat.Base using (suc; zero; _+_)

open import Surface.WellScoped
open import Surface.WellScoped.Substitution using ([_↦τ_]_; [_↦ε_]_; [_↦c_]_; [_↦Γ_]_)

-- It's interesting to note that _⊂_ does not work as nicely to express the notion of a prefix of a context.
-- Indeed, the information that the last element of the supercontext can be chopped off is lost:
-- _⊂_ can also imply that arbitrary bindings are inserted in the middle of the context, not necessarily appended to it.
-- We could have used _⊂_ with an extra requirement that ρ : Fin ℓ → Fin ℓ' is such that ∀ x → toℕ x ≡ toℕ (ρ x),
-- but it gets super messy really soon. For example, even proving that if ℓ' ≠ ℓ,
-- then extra elements were appended to the supercontext, is non-trivial.
-- It's perhaps cleanest and cheapest to just add an extra predicate.

infix 3 _prefix-at_of_
data _prefix-at_of_ : (Γ : Ctx ℓ) → (k : ℕ) → (Γ' : Ctx (k + ℓ)) → Set where
  prefix-refl : Γ prefix-at zero of Γ
  prefix-cons : ∀ {k} {Γ : Ctx ℓ} {Γ' : Ctx (k + ℓ)} {τ : SType (k + ℓ)}
              → Γ prefix-at k of Γ'
              → Γ prefix-at (suc k) of (Γ' , τ)

prefix-subst : ∀ {k} {Γ : Ctx ℓ} {Γ' : Ctx (suc k + ℓ)}
             → Γ prefix-at suc k of Γ'
             → Γ prefix-at k of ([ ℓ ↦Γ ε ] Γ')
prefix-subst {k = zero} (prefix-cons prefix) = prefix
prefix-subst {k = suc k} (prefix-cons prefix) = prefix-cons (prefix-subst prefix)
