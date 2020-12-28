{-# OPTIONS --safe #-}

module Surface.Operational.Lemmas where

open import Data.Fin using (zero; suc)
open import Data.Vec using (lookup; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Fin.Extra
open import Surface.WellScoped
open import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.Substitution as S
open import Surface.WellScoped.Substitution.Distributivity
open import Surface.Operational

ρ-preserves-values : {ρ : Fin ℓ → Fin ℓ'}
                   → IsValue ϖ
                   → IsValue (R.act-ε ρ ϖ)
ρ-preserves-values IV-Abs = IV-Abs
ρ-preserves-values IV-Unit = IV-Unit
ρ-preserves-values (IV-ADT is-value) = IV-ADT (ρ-preserves-values is-value)

ρ-↦ₘ-comm : {ρ : Fin ℓ → Fin ℓ'}
          → Monotonic ρ
          → ∀ ι ε
          → (bs : CaseBranches (Mkℕₐ n) ℓ)
          → (let branch = CaseBranch.body (lookup bs ι))
          → R.act-ε ρ ([ ι ↦ₘ ε ] bs) ≡ [ ι ↦ₘ R.act-ε ρ ε ] R.act-branches ρ bs
ρ-↦ₘ-comm {ρ = ρ} ρ-mono ι ε bs rewrite ρ-subst-distr-ε-0 _ ρ-mono ε (CaseBranch.body (lookup bs ι))
                                      | R.branch-lookup-comm ρ ι bs
                                      = refl

ρ-preserves-↝ : {ρ : Fin ℓ → Fin ℓ'}
              → Monotonic ρ
              → ε ↝ ε'
              → R.act-ε ρ ε ↝ R.act-ε ρ ε'
ρ-preserves-↝ ρ-mono (E-AppL ε↝ε') = E-AppL (ρ-preserves-↝ ρ-mono ε↝ε')
ρ-preserves-↝ ρ-mono (E-AppR is-value ε↝ε') = E-AppR (ρ-preserves-values is-value) (ρ-preserves-↝ ρ-mono ε↝ε')
ρ-preserves-↝ ρ-mono (E-AppAbs {ϖ = ϖ} {ε = ε} is-value) rewrite ρ-subst-distr-ε-0 _ ρ-mono ϖ ε = E-AppAbs (ρ-preserves-values is-value)
ρ-preserves-↝ ρ-mono (E-ADT ε↝ε') = E-ADT (ρ-preserves-↝ ρ-mono ε↝ε')
ρ-preserves-↝ ρ-mono (E-CaseScrut ε↝ε') = E-CaseScrut (ρ-preserves-↝ ρ-mono ε↝ε')
ρ-preserves-↝ ρ-mono (E-CaseMatch {ϖ = ϖ} {bs = bs} is-value idx)
  rewrite ρ-↦ₘ-comm ρ-mono idx ϖ bs
        = E-CaseMatch (ρ-preserves-values is-value) idx
