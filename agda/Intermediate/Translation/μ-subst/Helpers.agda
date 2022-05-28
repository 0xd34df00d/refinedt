{-# OPTIONS --safe #-}

module Intermediate.Translation.μ-subst.Helpers where

open import Data.Fin.Base using (zero; suc; raise)
open import Data.Nat.Base using (zero; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Data.Fin.Extra

open import Core.Syntax as C renaming (Γ to Γᶜ; ε to εᶜ; τ to τᶜ)
open import Core.Syntax.Derived as C
open import Core.Syntax.Renaming as CR
open import Core.Syntax.Renaming.Distributivity as CR
open import Core.Syntax.Substitution as CS
open import Core.Syntax.Substitution.Distributivity as CS

private
  m<n-⇒-ext-suc-n≡suc-n : {m n : Fin (suc ℓ)}
                        → m < n
                        → suc n ≡ CR.ext suc n
  m<n-⇒-ext-suc-n≡suc-n (<-zero _) = refl
  m<n-⇒-ext-suc-n≡suc-n (<-suc _) = refl

act-ε-lemma₁ : ∀ ι₀ (εᶜ : CExpr ℓ)
             → ∀ ι
             → CS.ext (CS.ext (CS.replace-at ι₀ εᶜ)) (CR.ext suc ι)
               ≡
               CR.act-ε (CR.ext suc) (CS.replace-at (suc ι₀) (CR.act-ε suc εᶜ) ι)
act-ε-lemma₁ ι₀ εᶜ zero = refl
act-ε-lemma₁ ι₀ εᶜ (suc ι) with ι₀ <>? ι
... | less m<n rewrite m<n-n-pred-cancel m<n
                     | m<n-⇒-ext-suc-n≡suc-n m<n
                     = refl
... | equal refl rewrite CR.act-ε-distr suc suc εᶜ
                       | CR.act-ε-distr suc (CR.ext suc) εᶜ
                       = refl
... | greater m>n = refl
