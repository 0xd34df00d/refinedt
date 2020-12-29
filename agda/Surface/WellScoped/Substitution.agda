{-# OPTIONS --safe #-}

module Surface.WellScoped.Substitution where

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Fin using (Fin; suc; zero; toℕ)
open import Data.Vec
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Fin.Extra
open import Surface.WellScoped
import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.Actions (record { Target = STerm
                                               ; var-action = λ σ idx → σ idx
                                               ; ext = λ where _ zero → SVar zero
                                                               σ (suc n) → R.weaken-ε (σ n)
                                               }
                                       ) public

replace-at : Fin (suc ℓ) → STerm ℓ → Fin (suc ℓ) → STerm ℓ
replace-at replace-idx ε var-idx with replace-idx <>? var-idx
-- replacement index is less than current variable index, so the variable points to a binder that just got closer to it,
-- so decrement the variable index:
... | less rep<var = SVar (m<n-n-pred rep<var)
-- just replace the current variable with the term:
... | equal m≡n = ε
-- replacement index is greater than current variable index, so the variable still refers to the same binder,
-- so leave the var index as-is, just shrinking the bound of Fin as the binders count just decremented:
... | greater rep>var = SVar (tighten rep>var)

SubstOn : (ℕ → Set) → Set
SubstOn Ty = ∀ {ℓ} → Fin (suc ℓ) → STerm ℓ → Ty (suc ℓ) → Ty ℓ

infixr 6 [_↦τ_]_ [_↦ρ_]_ [_↦ε_]_ [_↦c_]_ [_↦bs_]_
[_↦τ_]_ : SubstOn SType
[_↦τ_]_ idx ε = act-τ (replace-at idx ε)

[_↦ρ_]_ : SubstOn Refinement
[_↦ρ_]_ idx ε = act-ρ (replace-at idx ε)

[_↦ε_]_ : SubstOn STerm
[_↦ε_]_ idx ε = act-ε (replace-at idx ε)

[_↦c_]_ : SubstOn (ADTCons nₐ)
[_↦c_]_ idx ε = act-cons (replace-at idx ε)

[_↦bs_]_ : SubstOn (CaseBranches nₐ)
[_↦bs_]_ idx ε = act-branches (replace-at idx ε)


branch-lookup-comm : (σ : Fin (suc ℓ) → STerm ℓ)
                   → (ι : Fin n)
                   → (bs : CaseBranches (Mkℕₐ n) (suc ℓ))
                   → act-ε (ext σ) (CaseBranch.body (lookup bs ι)) ≡ CaseBranch.body (lookup (act-branches σ bs) ι)
branch-lookup-comm σ zero (_ ∷ _) = refl
branch-lookup-comm σ (suc ι) (_ ∷ bs) = branch-lookup-comm σ ι bs


≡-ext : {f₁ f₂ : Fin ℓ → STerm ℓ'}
      → (∀ x → f₁ x ≡ f₂ x)
      → (∀ x → ext f₁ x ≡ ext f₂ x)
≡-ext x-≡ zero = refl
≡-ext x-≡ (suc x) rewrite x-≡ x = refl

var-action-cong : {f₁ f₂ : Fin ℓ → STerm ℓ'}
                → (∀ x → f₁ x ≡ f₂ x)
                → (∀ x → var-action f₁ x ≡ var-action f₂ x)
var-action-cong x-≡ x = x-≡ x

open import Surface.WellScoped.ActionsLemmas var-action-record
                                             record { ≡-ext = ≡-ext
                                                    ; var-action-cong = var-action-cong
                                                    }
                                             public

infix 2 _f≡_
_f≡_ : ∀ {A B : Set} (f₁ f₂ : A → B) → Set
f₁ f≡ f₂ = ∀ x → f₁ x ≡ f₂ x

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

R-ext-replace-comm : ∀ ε (ρ : Fin ℓ → Fin ℓ') ι
                   → ext (replace-at (R.ext ρ ι) (R.act-ε ρ ε)) f≡ replace-at (suc (R.ext ρ ι)) (R.act-ε (R.ext ρ) (R.act-ε suc ε))
R-ext-replace-comm ε ρ zero zero = refl
R-ext-replace-comm ε ρ (suc ι) zero = refl
R-ext-replace-comm ε ρ zero (suc var-idx) with zero <>? var-idx
... | less m<n rewrite m<n-n-pred-cancel m<n = refl
... | equal refl rewrite R.weaken-ε-comm ρ ε = refl
R-ext-replace-comm ε ρ (suc ι) (suc var-idx) with suc (ρ ι) <>? var-idx
... | less m<n rewrite m<n-n-pred-cancel m<n = refl
... | equal refl rewrite R.weaken-ε-comm ρ ε = refl
... | greater m>n = refl

weaken-replace-comm : ∀ ε (ι : Fin (suc ℓ))
                    → R.weaken-ε ∘ replace-at ι ε f≡ replace-at (suc ι) (R.weaken-ε ε) ∘ suc
weaken-replace-comm ε zero zero = refl
weaken-replace-comm ε zero (suc x) = refl
weaken-replace-comm ε (suc ι) zero = refl
weaken-replace-comm ε (suc ι) (suc x) with ι <>? x
... | less m<n = refl
... | equal refl = refl
... | greater m>n = refl


ctx-idx : ∀ k → Fin (suc (k + ℓ))
ctx-idx zero = zero
ctx-idx (suc k) = suc (ctx-idx k)

-- Substitution on contexts: this is essentially replacing Γ, x ⦂ σ, Δ with Γ, [ x ↦ ε ] Δ
-- Here, ℓ is the length of Γ (which ε must live in), and k is the length of Δ.
[_↦Γ_]_ : ∀ {k} ℓ
        → (ε : STerm ℓ)
        → Ctx (suc k + ℓ)
        → Ctx (k + ℓ)
[_↦Γ_]_ {k = zero} ℓ ε (Γ , _) = Γ
[_↦Γ_]_ {k = suc k} ℓ ε (Γ,Δ , τ) = ([ ℓ ↦Γ ε ] Γ,Δ) , ([ ctx-idx k ↦τ R.weaken-ε-k k ε ] τ)
