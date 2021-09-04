{-# OPTIONS --safe #-}

module Surface.Operational.Lemmas where

open import Data.Fin using (zero; suc)
open import Data.Vec using (lookup; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Data.Fin.Extra
open import Surface.Syntax
open import Surface.Syntax.Renaming as R
open import Surface.Syntax.Substitution as S
open import Surface.Syntax.Substitution.Commutativity
open import Surface.Syntax.Substitution.Distributivity as S
open import Surface.Syntax.Substitution.Stable
open import Surface.Operational

ρ-preserves-values : {ρ : Fin ℓ → Fin ℓ'}
                   → IsValue ϖ
                   → IsValue (R.act-ε ρ ϖ)
ρ-preserves-values IV-Abs = IV-Abs
ρ-preserves-values IV-Unit = IV-Unit
ρ-preserves-values (IV-ADT is-value) = IV-ADT (ρ-preserves-values is-value)

σ-preserves-values : {σ : Fin (suc ℓ) → STerm ℓ}
                   → IsValue ϖ
                   → IsValue (S.act-ε σ ϖ)
σ-preserves-values IV-Abs = IV-Abs
σ-preserves-values IV-Unit = IV-Unit
σ-preserves-values (IV-ADT is-value) = IV-ADT (σ-preserves-values is-value)

ρ-↦ₘ-comm : (ρ : Fin ℓ → Fin ℓ')
          → ∀ ι ε
          → (bs : CaseBranches (Mkℕₐ n) ℓ)
          → R.act-ε ρ ([ ι ↦ₘ ε ] bs) ≡ [ ι ↦ₘ R.act-ε ρ ε ] R.act-branches ρ bs
ρ-↦ₘ-comm ρ ι ε bs rewrite ρ-subst-distr-ε-0 ρ ε (CaseBranch.body (lookup bs ι))
                         | R.branch-lookup-comm ρ ι bs
                         = refl

σ-replace-comm : (σ : Fin (suc ℓ) → STerm ℓ)
               → ∀ ε
               → ∀ x → S.act-ε σ (replace-at zero ε x) ≡ S.act-ε (replace-at zero (S.act-ε σ ε)) (S.ext σ x)
σ-replace-comm σ ε zero = refl
σ-replace-comm σ ε (suc x) rewrite replace-weakened-ε-zero (S.act-ε σ ε) (σ x) = refl

σ-↦ₘ-comm : (σ : Fin (suc ℓ) → STerm ℓ)
          → ∀ ι ε
          → (bs : CaseBranches (Mkℕₐ n) (suc ℓ))
          → S.act-ε σ ([ ι ↦ₘ ε ] bs) ≡ [ ι ↦ₘ S.act-ε σ ε ] S.act-branches σ bs
σ-↦ₘ-comm σ ι ε bs rewrite sym (S.branch-lookup-comm σ ι bs)
                         | S.act-ε-distr (replace-at zero ε) σ (CaseBranch.body (lookup bs ι))
                         | S.act-ε-distr (S.ext σ) (replace-at zero (S.act-ε σ ε)) (CaseBranch.body (lookup bs ι))
                         | S.act-ε-extensionality (σ-replace-comm σ ε) (CaseBranch.body (lookup bs ι))
                         = refl

ρ-preserves-↝ : (ρ : Fin ℓ → Fin ℓ')
              → ε ↝ ε'
              → R.act-ε ρ ε ↝ R.act-ε ρ ε'
ρ-preserves-↝ ρ (E-AppL ε↝ε') = E-AppL (ρ-preserves-↝ ρ ε↝ε')
ρ-preserves-↝ ρ (E-AppAbs {ε = ε} {ε' = ε'})
  rewrite ρ-subst-distr-ε-0 ρ ε' ε
        = E-AppAbs
ρ-preserves-↝ ρ (E-ADT ε↝ε') = E-ADT (ρ-preserves-↝ ρ ε↝ε')
ρ-preserves-↝ ρ (E-CaseScrut ε↝ε') = E-CaseScrut (ρ-preserves-↝ ρ ε↝ε')
ρ-preserves-↝ ρ (E-CaseMatch {ϖ = ϖ} {bs = bs} is-value ι)
  rewrite ρ-↦ₘ-comm ρ ι ϖ bs
        = E-CaseMatch (ρ-preserves-values is-value) ι

subst-preserves-↝ : ∀ ι ε₀
                  → ε ↝ ε'
                  → ([ ι ↦ε ε₀ ] ε) ↝ ([ ι ↦ε ε₀ ] ε')
subst-preserves-↝ ι ε₀ (E-AppL ε↝ε') = E-AppL (subst-preserves-↝ ι ε₀ ε↝ε')
subst-preserves-↝ ι ε₀ (E-AppAbs {ε = ε} {ε' = ε'})
  rewrite subst-commutes-ε-zero ι ε₀ ε' ε
        | S.act-ε-extensionality (ext-replace-comm ε₀ ι) ε
        = E-AppAbs
subst-preserves-↝ ι ε₀ (E-ADT ε↝ε') = E-ADT (subst-preserves-↝ ι ε₀ ε↝ε')
subst-preserves-↝ ι ε₀ (E-CaseScrut ε↝ε') = E-CaseScrut (subst-preserves-↝ ι ε₀ ε↝ε')
subst-preserves-↝ ι ε₀ (E-CaseMatch {ϖ = ϖ} {bs = bs} is-value ι')
  rewrite σ-↦ₘ-comm (replace-at ι ε₀) ι' ϖ bs
        = E-CaseMatch (σ-preserves-values is-value) ι'
