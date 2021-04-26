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
open import Surface.Syntax.Shape
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
[_↦τ_]_ idx ε = act-τ (replace-at idx ε)

[_↦ρ_]_ : SubstOn Refinement
[_↦ρ_]_ idx ε = act-ρ (replace-at idx ε)

[_↦ε_]_ : SubstOn STerm
[_↦ε_]_ idx ε = act-ε (replace-at idx ε)

[_↦c_]_ : SubstOn (ADTCons nₐ)
[_↦c_]_ idx ε = act-cons (replace-at idx ε)

[_↦bs_]_ : SubstOn (CaseBranches nₐ)
[_↦bs_]_ idx ε = act-branches (replace-at idx ε)

↦τ-preserves-shape : ∀ ι (ε : STerm ℓ)
                   → ShapePreserving (λ τ' τ → τ' ≡ [ ι ↦τ ε ] τ)
↦τ-preserves-shape _ _ {τ₂ = ⟨ _ ∣ _ ⟩} refl = refl
↦τ-preserves-shape _ _ {τ₂ = _ ⇒ _} refl = refl
↦τ-preserves-shape _ _ {τ₂ = ⊍ _} refl = refl

branch-lookup-comm : (σ : Fin (suc ℓ) → STerm ℓ)
                   → (ι : Fin n)
                   → (bs : CaseBranches (Mkℕₐ n) (suc ℓ))
                   → act-ε (ext σ) (CaseBranch.body (lookup bs ι)) ≡ CaseBranch.body (lookup (act-branches σ bs) ι)
branch-lookup-comm σ zero (_ ∷ _) = refl
branch-lookup-comm σ (suc ι) (_ ∷ bs) = branch-lookup-comm σ ι bs


ext-id : ∀ {f : Fin ℓ → STerm ℓ}
       → (∀ x → var-action (f x) ≡ SVar x)
       → (∀ x → var-action (ext f x) ≡ SVar x)
ext-id f-≡ zero = refl
ext-id f-≡ (suc x) rewrite f-≡ x = refl

open import Surface.Syntax.ActionsLemmas var-action-record
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


ctx-idx : ∀ k → Fin (suc (k + ℓ))
ctx-idx zero = zero
ctx-idx (suc k) = suc (ctx-idx k)

-- Substitution on contexts: this is essentially replacing Γ, x ⦂ σ, Δ with Γ, [ x ↦ ε ] Δ
-- Here, ℓ is the length of Γ (which ε must live in), and k is the length of Δ.
[_↦Γ_]_ : ∀ ℓ
        → (ε : STerm ℓ)
        → Ctx (suc k + ℓ)
        → Ctx (k + ℓ)
[_↦Γ_]_ {k = zero} ℓ ε (Γ , _) = Γ
[_↦Γ_]_ {k = suc k} ℓ ε (Γ,Δ , τ) = ([ ℓ ↦Γ ε ] Γ,Δ) , ([ ctx-idx k ↦τ R.weaken-ε-k k ε ] τ)
