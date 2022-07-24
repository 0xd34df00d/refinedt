{-# OPTIONS --safe #-}

module Surface.Syntax.Substitution where

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Fin using (Fin; suc; zero; toℕ)
open import Data.Vec
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Common.Helpers
open import Data.Fin.Extra
open import Surface.Syntax
import      Surface.Syntax.Renaming as R
open import Surface.Syntax.Actions (record { Target = STerm
                                           ; var-action = λ ε → ε
                                           ; ext = λ where _ zero → SVar zero
                                                           σ (suc n) → R.weaken-ε (σ n)
                                           }
                                   ) public

replace-at : Fin (suc ℓ) → STerm ℓ → Fin (suc ℓ) → STerm ℓ
replace-at = replace-at-generic SVar

SubstOn : (ℕ → Set) → Set
SubstOn Ty = ∀ {ℓ} → Fin (suc ℓ) → STerm ℓ → Ty (suc ℓ) → Ty ℓ

infixr 6 [_↦τ_]_ [_↦ρ_]_ [_↦ε_]_ [_↦c_]_ [_↦bs_]_
[_↦τ_]_ : SubstOn SType
[_↦τ_]_ ι ε = act-τ (replace-at ι ε)

[_↦ρ_]_ : SubstOn Refinement
[_↦ρ_]_ ι ε = act-ρ (replace-at ι ε)

[_↦ε_]_ : SubstOn STerm
[_↦ε_]_ ι ε = act-ε (replace-at ι ε)

[_↦c_]_ : SubstOn (ADTCons nₐ)
[_↦c_]_ ι ε = act-cons (replace-at ι ε)

[_↦bs_]_ : SubstOn (CaseBranches nₐ)
[_↦bs_]_ ι ε = act-branches (replace-at ι ε)

branch-lookup-comm : (σ : Fin (suc ℓ) → STerm ℓ)
                   → (ι : Fin n)
                   → (bs : CaseBranches (Mkℕₐ n) (suc ℓ))
                   → act-ε (ext σ) (CaseBranch.body (lookup bs ι)) ≡ CaseBranch.body (lookup (act-branches σ bs) ι)
branch-lookup-comm σ zero (_ ∷ _) = refl
branch-lookup-comm σ (suc ι) (_ ∷ bs) = branch-lookup-comm σ ι bs

cons-lookup-comm : (σ : Fin (suc ℓ) → STerm ℓ)
                 → (ι : Fin n)
                 → (cons : ADTCons (Mkℕₐ n) (suc ℓ))
                 → act-τ σ (lookup cons ι) ≡ lookup (act-cons σ cons) ι
cons-lookup-comm σ zero (τ ∷ _) = refl
cons-lookup-comm σ (suc ι) (_ ∷ cons) = cons-lookup-comm σ ι cons


ext-id : ∀ {f : Fin ℓ → STerm ℓ}
       → (∀ x → var-action (f x) ≡ SVar x)
       → (∀ x → var-action (ext f x) ≡ SVar x)
ext-id f-≡ zero = refl
ext-id f-≡ (suc x) rewrite f-≡ x = refl

open import Surface.Syntax.Actions.Lemmas var-action-record
                                          record { ≡-ext = λ where x-≡ zero → refl
                                                                   x-≡ (suc x) → cong R.weaken-ε (x-≡ x)
                                                 ; ext-id = ext-id
                                                 }
                                          public

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


-- Substitution on contexts: this is essentially replacing Γ, x ⦂ σ, Δ with Γ, [ x ↦ ε ] Δ
-- Here, ℓ is the length of Γ (which ε must live in), and k is the length of Δ.
[_↦Γ_]_ : ∀ ℓ
        → (ε : STerm ℓ)
        → Ctx (suc k + ℓ)
        → Ctx (k + ℓ)
[_↦Γ_]_ {k = zero} ℓ ε (Γ , _) = Γ
[_↦Γ_]_ {k = suc k} ℓ ε (Γ,Δ , τ) = ([ ℓ ↦Γ ε ] Γ,Δ) , ([ ctx-idx k ↦τ R.weaken-ε-k k ε ] τ)

-- Substitutions within a context by a term in a smaller context.
-- These are basically the substitutions without '<', but with a bit different indexing.
[_↦τ<_]_ : ∀ ℓ
         → (ε : STerm ℓ) → SType (suc k + ℓ) → SType (k + ℓ)
[_↦τ<_]_ {k = k} _ ε τ = [ ctx-idx k ↦τ R.weaken-ε-k _ ε ] τ

[_↦ε<_]_ : ∀ ℓ
         → (ε : STerm ℓ) → STerm (suc k + ℓ) → STerm (k + ℓ)
[_↦ε<_]_ {k = k} _ ε ε' = [ ctx-idx k ↦ε R.weaken-ε-k _ ε ] ε'

[_↦c<_]_ : ∀ ℓ
         → (ε : STerm ℓ) → ADTCons nₐ (suc k + ℓ) → ADTCons nₐ (k + ℓ)
[_↦c<_]_ {k = k} _ ε cons = [ ctx-idx k ↦c R.weaken-ε-k _ ε ] cons

[_↦bs<_]_ : ∀ ℓ
         → (ε : STerm ℓ) → CaseBranches nₐ (suc k + ℓ) → CaseBranches nₐ (k + ℓ)
[_↦bs<_]_ {k = k} _ ε bs = [ ctx-idx k ↦bs R.weaken-ε-k _ ε ] bs


first-↦τ< : (ε : STerm ℓ)
          → (τ : SType (suc ℓ))
          → [ ℓ ↦τ< ε ] τ ≡ [ zero ↦τ ε ] τ
first-↦τ< ε τ = act-τ-extensionality (λ ι → cong (λ ε → replace-at zero ε ι) (R.act-ε-id (λ _ → refl) ε)) τ
