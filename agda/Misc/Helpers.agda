module Misc.Helpers where

open import Agda.Builtin.Equality
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any

∈-swap : {a : Set} → ∀ {xs₁ xs₂} {x x₁ x₂ : a}
       → x ∈ (xs₁ ++ x₁ ∷ x₂ ∷ xs₂)
       → x ∈ (xs₁ ++ x₂ ∷ x₁ ∷ xs₂)
∈-swap {xs₁ = []} (here px) = there (here px)
∈-swap {xs₁ = []} (there (here px)) = here px
∈-swap {xs₁ = []} (there (there rest)) = there (there rest)
∈-swap {xs₁ = x ∷ xs₁} (here px) = here px
∈-swap {xs₁ = x ∷ xs₁} (there prf) = there (∈-swap prf)
