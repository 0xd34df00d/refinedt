{-# OPTIONS --safe #-}

module Core.Syntax.Substitution where

open import Data.Nat using (suc; zero)
open import Data.Fin using (suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Common.Helpers
open import Data.Fin.Extra
open import Core.Syntax
import      Core.Syntax.Renaming as R
open import Core.Syntax.Actions (record { Target = CExpr
                                        ; var-action = λ ε → ε
                                        ; ext = λ where _ zero → CVar zero
                                                        σ (suc n) → R.weaken-ε (σ n)
                                        }) public

ext-id-lemma : ∀ {f : Fin ℓ → Target ℓ}
             → (f f≡ CVar)
             → (ext f f≡ CVar)
ext-id-lemma f-id zero = refl
ext-id-lemma f-id (suc ι) rewrite f-id ι = refl

open import Core.Syntax.Actions.Lemmas var-action-record (record { ≡-ext = λ where x-≡ zero → refl
                                                                                   x-≡ (suc ι) → cong R.weaken-ε (x-≡ ι)
                                                                 ; ext-id = ext-id-lemma
                                                                 }) public

replace-at : Fin (suc ℓ) → CExpr ℓ → Fin (suc ℓ) → CExpr ℓ
replace-at = replace-at-generic CVar

SubstOn : (ℕ → Set) → Set
SubstOn Ty = ∀ {ℓ} → Fin (suc ℓ) → CExpr ℓ → Ty (suc ℓ) → Ty ℓ

infixr 6 [_↦_]_ [_↦c_]_ [_↦bs_]_
[_↦_]_ : SubstOn CExpr
[_↦_]_ idx ε = act-ε (replace-at idx ε)

[_↦c_]_ : SubstOn (ADTCons nₐ)
[_↦c_]_ idx ε = act-cons (replace-at idx ε)

[_↦bs_]_ : SubstOn (CaseBranches nₐ)
[_↦bs_]_ idx ε = act-branches (replace-at idx ε)

ext-replace-comm : ∀ ε (ι : Fin (suc ℓ))
                 → ext (replace-at ι ε) f≡ replace-at (suc ι) (R.act-ε suc ε)
ext-replace-comm _ zero zero = refl
ext-replace-comm _ (suc ι) zero = refl
ext-replace-comm _ zero (suc var-idx) with zero <>? var-idx
... | less m<n rewrite m<n-n-pred-cancel m<n = refl
... | equal refl = refl
ext-replace-comm _ (suc ι) (suc var-idx) with suc ι <>? var-idx
... | less m<n rewrite m<n-n-pred-cancel m<n = refl
... | equal refl = refl
... | greater m>n = refl


-- Tail-invariant substitution
TailInvariantSubstOn : (ℕ → Set) → Set
TailInvariantSubstOn Ty = ∀ {k} ℓ → (ε : CExpr ℓ) → Ty (suc k + ℓ) → Ty (k + ℓ)

[_↦'_]_ : TailInvariantSubstOn CExpr
[_↦'_]_ {k = k} _ ε τ = [ ctx-idx k ↦ R.weaken-ε-k _ ε ] τ

[_↦c'_]_ : TailInvariantSubstOn (ADTCons nₐ)
[_↦c'_]_ {k = k} _ ε cons = [ ctx-idx k ↦c R.weaken-ε-k _ ε ] cons

[_↦bs'_]_ : TailInvariantSubstOn (CaseBranches nₐ)
[_↦bs'_]_ {k = k} _ ε bs = [ ctx-idx k ↦bs R.weaken-ε-k _ ε ] bs

CΠ-↦'-distr : ∀ ℓ (ε : CExpr ℓ) (ε₁ : CExpr (suc k + ℓ)) ε₂
            → [ ℓ ↦' ε ] CΠ ε₁ ε₂ ≡ CΠ ([ ℓ ↦' ε ] ε₁) ([ ℓ ↦' ε ] ε₂)
CΠ-↦'-distr {k = k} _ ε _ ε₂
  rewrite act-ε-extensionality (ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) ε₂
        = refl

CLam-↦'-distr : ∀ ℓ (ε : CExpr ℓ) (ε₁ : CExpr (suc k + ℓ)) ε₂
              → [ ℓ ↦' ε ] CLam ε₁ ε₂ ≡ CLam ([ ℓ ↦' ε ] ε₁) ([ ℓ ↦' ε ] ε₂)
CLam-↦'-distr {k = k} _ ε _ ε₂
  rewrite act-ε-extensionality (ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) ε₂
        = refl
