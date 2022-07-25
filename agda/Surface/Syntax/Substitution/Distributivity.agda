{-# OPTIONS --safe #-}

module Surface.Syntax.Substitution.Distributivity where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; suc; zero; raise; toℕ; fromℕ)
open import Data.Fin.Properties using (toℕ-injective; suc-injective)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Vec
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import Common.Helpers
open import Common.Types
open import Data.Fin.Extra
open import Surface.Syntax
open import Surface.Syntax.Substitution as S
import Surface.Syntax.Renaming as R

R-ext-ext-commutes-ε : (ρ : Fin ℓ₁ → Fin ℓ₂)
                     → (σ : Fin ℓ₀ → STerm ℓ₁)
                     → ∀ x → R.act-ε (R.ext ρ) (ext σ x) ≡ ext (R.act-ε ρ ∘ σ) x
R-ext-ext-commutes-ε ρ σ zero = refl
R-ext-ext-commutes-ε ρ σ (suc x)
  rewrite R.act-ε-distr suc (R.ext ρ) (σ x)
        | R.act-ε-distr ρ suc (σ x)
        = refl

ρ-σ-Distributivity : {Ty : ℕ → Set} → R.ActionOn Ty → ActionOn Ty → Set
ρ-σ-Distributivity {Ty} ρ-act σ-act = ∀ {ℓ₀ ℓ₁ ℓ₂}
                                      → (ρ : Fin ℓ₁ → Fin ℓ₂)
                                      → (σ : Fin ℓ₀ → STerm ℓ₁)
                                      → (v : Ty ℓ₀)
                                      → ρ-act ρ (σ-act σ v) ≡ σ-act (R.act-ε ρ ∘ σ) v

mutual
  ρ-σ-distr-τ : ρ-σ-Distributivity R.act-τ act-τ
  ρ-σ-distr-τ ρ σ ⟨ b ∣ ρ' ⟩
    rewrite ρ-σ-distr-ρ (R.ext ρ) (ext σ) ρ'
          | act-ρ-extensionality (R-ext-ext-commutes-ε ρ σ) ρ'
          = refl
  ρ-σ-distr-τ ρ σ (τ₁ ⇒ τ₂)
    rewrite ρ-σ-distr-τ ρ σ τ₁
          | ρ-σ-distr-τ (R.ext ρ) (ext σ) τ₂
          | act-τ-extensionality (R-ext-ext-commutes-ε ρ σ) τ₂
          = refl
  ρ-σ-distr-τ ρ σ (⊍ cons) rewrite ρ-σ-distr-cons ρ σ cons = refl

  ρ-σ-distr-ρ : ρ-σ-Distributivity R.act-ρ act-ρ
  ρ-σ-distr-ρ ρ σ (ε₁ ≈ ε₂ of τ)
    rewrite ρ-σ-distr-ε ρ σ ε₁
          | ρ-σ-distr-ε ρ σ ε₂
          | ρ-σ-distr-τ ρ σ τ
          = refl
  ρ-σ-distr-ρ ρ σ (ρ₁ ∧ ρ₂)
    rewrite ρ-σ-distr-ρ ρ σ ρ₁
          | ρ-σ-distr-ρ ρ σ ρ₂
          = refl
  ρ-σ-distr-ρ _ _ Τ = refl

  ρ-σ-distr-ε : ρ-σ-Distributivity R.act-ε act-ε
  ρ-σ-distr-ε ρ σ SUnit = refl
  ρ-σ-distr-ε ρ σ (SVar ι) = refl
  ρ-σ-distr-ε ρ σ (SLam τ ε)
    rewrite ρ-σ-distr-τ ρ σ τ
          | ρ-σ-distr-ε (R.ext ρ) (ext σ) ε
          | act-ε-extensionality (R-ext-ext-commutes-ε ρ σ) ε
          = refl
  ρ-σ-distr-ε ρ σ (SApp ε₁ ε₂)
    rewrite ρ-σ-distr-ε ρ σ ε₁
          | ρ-σ-distr-ε ρ σ ε₂
          = refl
  ρ-σ-distr-ε ρ σ (SCase ε cons τ branches)
    rewrite ρ-σ-distr-ε ρ σ ε
          | ρ-σ-distr-cons ρ σ cons
          | ρ-σ-distr-τ ρ σ τ
          | ρ-σ-distr-branches ρ σ branches
          = refl
  ρ-σ-distr-ε ρ σ (SCon ι ε cons)
    rewrite ρ-σ-distr-ε ρ σ ε
          | ρ-σ-distr-cons ρ σ cons
          = refl

  ρ-σ-distr-cons : ρ-σ-Distributivity {ADTCons nₐ} R.act-cons act-cons
  ρ-σ-distr-cons ρ σ [] = refl
  ρ-σ-distr-cons ρ σ (τ ∷ cons)
    rewrite ρ-σ-distr-τ ρ σ τ
          | ρ-σ-distr-cons ρ σ cons
          = refl

  ρ-σ-distr-branches : ρ-σ-Distributivity {CaseBranches nₐ} R.act-branches act-branches
  ρ-σ-distr-branches ρ σ [] = refl
  ρ-σ-distr-branches ρ σ (MkCaseBranch ε ∷ bs)
    rewrite ρ-σ-distr-ε (R.ext ρ) (ext σ) ε
          | ρ-σ-distr-branches ρ σ bs
          | act-ε-extensionality (R-ext-ext-commutes-ε ρ σ) ε
          = refl

σ-ρ-Distributivity : {Ty : ℕ → Set} → ActionOn Ty → R.ActionOn Ty → Set
σ-ρ-Distributivity {Ty} σ-act ρ-act = ∀ {ℓ₀ ℓ₁ ℓ₂}
                                      → (σ : Fin ℓ₁ → STerm ℓ₂)
                                      → (ρ : Fin ℓ₀ → Fin ℓ₁)
                                      → (v : Ty ℓ₀)
                                      → σ-act σ (ρ-act ρ v) ≡ σ-act (σ ∘ ρ) v

ext-Rext-distr : (σ : Fin ℓ₁ → STerm ℓ₂)
               → (ρ : Fin ℓ₀ → Fin ℓ₁)
               → (∀ x → ext σ (R.ext ρ x) ≡ ext (σ ∘ ρ) x)
ext-Rext-distr σ ρ zero = refl
ext-Rext-distr σ ρ (suc x) = refl

mutual
  σ-ρ-distr-τ : σ-ρ-Distributivity act-τ R.act-τ
  σ-ρ-distr-τ σ ρ ⟨ b ∣ ρ' ⟩
    rewrite σ-ρ-distr-ρ (ext σ) (R.ext ρ) ρ'
          | act-ρ-extensionality (ext-Rext-distr σ ρ) ρ'
          = refl
  σ-ρ-distr-τ σ ρ (τ₁ ⇒ τ₂)
    rewrite σ-ρ-distr-τ σ ρ τ₁
          | σ-ρ-distr-τ (ext σ) (R.ext ρ) τ₂
          | act-τ-extensionality (ext-Rext-distr σ ρ) τ₂
          = refl
  σ-ρ-distr-τ σ ρ (⊍ cons) rewrite σ-ρ-distr-cons σ ρ cons = refl

  σ-ρ-distr-ρ : σ-ρ-Distributivity act-ρ R.act-ρ
  σ-ρ-distr-ρ σ ρ (ε₁ ≈ ε₂ of τ)
    rewrite σ-ρ-distr-ε σ ρ ε₁
          | σ-ρ-distr-ε σ ρ ε₂
          | σ-ρ-distr-τ σ ρ τ
          = refl
  σ-ρ-distr-ρ σ ρ (ρ₁ ∧ ρ₂)
    rewrite σ-ρ-distr-ρ σ ρ ρ₁
          | σ-ρ-distr-ρ σ ρ ρ₂
          = refl
  σ-ρ-distr-ρ _ _ Τ = refl

  σ-ρ-distr-ε : σ-ρ-Distributivity act-ε R.act-ε
  σ-ρ-distr-ε σ ρ SUnit = refl
  σ-ρ-distr-ε σ ρ (SVar ι) = refl
  σ-ρ-distr-ε σ ρ (SLam τ ε)
    rewrite σ-ρ-distr-τ σ ρ τ
          | σ-ρ-distr-ε (ext σ) (R.ext ρ) ε
          | act-ε-extensionality (ext-Rext-distr σ ρ) ε
          = refl
  σ-ρ-distr-ε σ ρ (SApp ε₁ ε₂)
    rewrite σ-ρ-distr-ε σ ρ ε₁
          | σ-ρ-distr-ε σ ρ ε₂
          = refl
  σ-ρ-distr-ε σ ρ (SCase ε cons τ branches)
    rewrite σ-ρ-distr-ε σ ρ ε
          | σ-ρ-distr-cons σ ρ cons
          | σ-ρ-distr-τ σ ρ τ
          | σ-ρ-distr-branches σ ρ branches
          = refl
  σ-ρ-distr-ε σ ρ (SCon ι ε cons)
    rewrite σ-ρ-distr-ε σ ρ ε
          | σ-ρ-distr-cons σ ρ cons
          = refl

  σ-ρ-distr-cons : σ-ρ-Distributivity {ADTCons nₐ} act-cons R.act-cons
  σ-ρ-distr-cons σ ρ [] = refl
  σ-ρ-distr-cons σ ρ (τ ∷ cons)
    rewrite σ-ρ-distr-τ σ ρ τ
          | σ-ρ-distr-cons σ ρ cons
          = refl

  σ-ρ-distr-branches : σ-ρ-Distributivity {CaseBranches nₐ} act-branches R.act-branches
  σ-ρ-distr-branches σ ρ [] = refl
  σ-ρ-distr-branches σ ρ (MkCaseBranch ε ∷ bs)
    rewrite σ-ρ-distr-ε (ext σ) (R.ext ρ) ε
          | σ-ρ-distr-branches σ ρ bs
          | act-ε-extensionality (ext-Rext-distr σ ρ) ε
          = refl


act-ε-ext-distr : (σ₁ : Fin ℓ₀ → STerm ℓ₁)
                → (σ₂ : Fin ℓ₁ → STerm ℓ₂)
                → (x : Fin (suc ℓ₀))
                → act-ε (ext σ₂) (ext σ₁ x) ≡ ext (act-ε σ₂ ∘ σ₁) x
act-ε-ext-distr σ₁ σ₂ zero = refl
act-ε-ext-distr σ₁ σ₂ (suc x)
  rewrite σ-ρ-distr-ε (ext σ₂) suc (σ₁ x)
        | ρ-σ-distr-ε suc σ₂ (σ₁ x)
        = refl

ActDistributivity : {Ty : ℕ → Set} → ActionOn Ty → Set
ActDistributivity {Ty} act = ∀ {ℓ₀ ℓ₁ ℓ₂}
                             → (σ₁ : Fin ℓ₀ → STerm ℓ₁)
                             → (σ₂ : Fin ℓ₁ → STerm ℓ₂)
                             → (v : Ty ℓ₀)
                             → act σ₂ (act σ₁ v) ≡ act (act-ε σ₂ ∘ σ₁) v

mutual
  act-τ-distr : ActDistributivity act-τ
  act-τ-distr σ₁ σ₂ ⟨ b ∣ ρ ⟩
    rewrite act-ρ-distr (ext σ₁) (ext σ₂) ρ
          | act-ρ-extensionality (act-ε-ext-distr σ₁ σ₂) ρ
          = refl
  act-τ-distr σ₁ σ₂ (τ₁ ⇒ τ₂)
    rewrite act-τ-distr σ₁ σ₂ τ₁
          | act-τ-distr (ext σ₁) (ext σ₂) τ₂
          | act-τ-extensionality (act-ε-ext-distr σ₁ σ₂) τ₂
          = refl
  act-τ-distr σ₁ σ₂ (⊍ cons) rewrite act-cons-distr σ₁ σ₂ cons = refl

  act-ρ-distr : ActDistributivity act-ρ
  act-ρ-distr σ₁ σ₂ (ε₁ ≈ ε₂ of τ)
    rewrite act-ε-distr σ₁ σ₂ ε₁
          | act-ε-distr σ₁ σ₂ ε₂
          | act-τ-distr σ₁ σ₂ τ
          = refl
  act-ρ-distr σ₁ σ₂ (ρ₁ ∧ ρ₂)
    rewrite act-ρ-distr σ₁ σ₂ ρ₁
          | act-ρ-distr σ₁ σ₂ ρ₂
          = refl
  act-ρ-distr _ _ Τ = refl

  act-ε-distr : ActDistributivity act-ε
  act-ε-distr σ₁ σ₂ SUnit = refl
  act-ε-distr σ₁ σ₂ (SVar ι) = refl
  act-ε-distr σ₁ σ₂ (SLam τ ε)
    rewrite act-τ-distr σ₁ σ₂ τ
          | act-ε-distr (ext σ₁) (ext σ₂) ε
          | act-ε-extensionality (act-ε-ext-distr σ₁ σ₂) ε
          = refl
  act-ε-distr σ₁ σ₂ (SApp ε₁ ε₂)
    rewrite act-ε-distr σ₁ σ₂ ε₁
          | act-ε-distr σ₁ σ₂ ε₂
          = refl
  act-ε-distr σ₁ σ₂ (SCase ε cons τ branches)
    rewrite act-ε-distr σ₁ σ₂ ε
          | act-cons-distr σ₁ σ₂ cons
          | act-τ-distr σ₁ σ₂ τ
          | act-branches-distr σ₁ σ₂ branches
          = refl
  act-ε-distr σ₁ σ₂ (SCon ι ε cons)
    rewrite act-ε-distr σ₁ σ₂ ε
          | act-cons-distr σ₁ σ₂ cons
          = refl

  act-cons-distr : ActDistributivity {ADTCons nₐ} act-cons
  act-cons-distr σ₁ σ₂ [] = refl
  act-cons-distr σ₁ σ₂ (τ ∷ cons)
    rewrite act-τ-distr σ₁ σ₂ τ
          | act-cons-distr σ₁ σ₂ cons
          = refl

  act-branches-distr : ActDistributivity {CaseBranches nₐ} act-branches
  act-branches-distr σ₁ σ₂ [] = refl
  act-branches-distr σ₁ σ₂ (MkCaseBranch ε ∷ bs)
    rewrite act-ε-distr (ext σ₁) (ext σ₂) ε
          | act-ε-extensionality (act-ε-ext-distr σ₁ σ₂) ε
          | act-branches-distr σ₁ σ₂ bs
          = refl


ρ-ιth : (ρ : Fin ℓ → Fin ℓ')
      → (ι : Fin (suc ℓ))
      → (Fin (suc ℓ) → Fin (suc ℓ'))
ρ-ιth ρ ι v with ι <>? v
... | less ι<v = suc (ρ (m<n-n-pred ι<v))
... | equal v≡ι = zero
... | greater ι>v = suc (ρ (tighten ι>v))

ρ-0th-is-ext : (ρ : Fin ℓ → Fin ℓ')
             → R.ext ρ f≡ ρ-ιth ρ zero
ρ-0th-is-ext ρ zero = refl
ρ-0th-is-ext ρ (suc var) = refl


-- This is not used elsewhere, just a sanity check that ρ-ιth makes sense
private
  tighten-not-pred : {v₁ v₂ ι : Fin (suc ℓ)}
                   → (v₁<ι : v₁ < ι)
                   → (ι<v₂ : ι < v₂)
                   → tighten v₁<ι ≡ m<n-n-pred ι<v₂
                   → ⊥
  tighten-not-pred {ℓ = suc ℓ} (<-zero n) (<-suc ι<v₂) refl = ⊥-elim (¬n<0 ι<v₂)
  tighten-not-pred {ℓ = suc ℓ} (<-suc v₁<ι) (<-suc ι<v₂) refl = ⊥-elim (<-antireflexive (a≤b<c (suc-tighten v₁<ι) ι<v₂))

  ρ-ιth-injective : ∀ ℓ'
                  → (ρ : Fin ℓ → Fin ℓ')
                  → (ι : Fin (suc ℓ))
                  → Injective ρ
                  → Injective (ρ-ιth ρ ι)
  ρ-ιth-injective _  ρ ι ρ-inj {x₁ = v₁} {x₂ = v₂} ≡-prf with ι <>? v₁ | ι <>? v₂
  ρ-ιth-injective _  ρ ι ρ-inj {x₁ = v₁} {x₂ = v₂} ≡-prf | greater m<n | greater m<n₁ = tighten-injective (ρ-inj (suc-injective ≡-prf))
  ρ-ιth-injective ℓ' ρ ι ρ-inj {x₁ = v₁} {x₂ = v₂} ≡-prf | greater m<n | equal refl with ≡-prf
  ... | ()
  ρ-ιth-injective _  ρ ι ρ-inj {x₁ = v₁} {x₂ = v₂} ≡-prf | greater m<n | less m>n = ⊥-elim (tighten-not-pred m<n m>n (ρ-inj (suc-injective ≡-prf)))
  ρ-ιth-injective ℓ' ρ ι ρ-inj {x₁ = v₁} {x₂ = v₂} ≡-prf | equal refl | greater m<n with ≡-prf
  ... | ()
  ρ-ιth-injective _  ρ ι ρ-inj {x₁ = v₁} {x₂ = v₂} ≡-prf | equal refl | equal refl = refl
  ρ-ιth-injective _  ρ ι ρ-inj {x₁ = v₁} {x₂ = v₂} ≡-prf | equal refl | less m>n with ≡-prf
  ... | ()
  ρ-ιth-injective _  ρ ι ρ-inj {x₁ = v₁} {x₂ = v₂} ≡-prf | less m>n | greater m<n = ⊥-elim (tighten-not-pred m<n m>n (ρ-inj (suc-injective (sym ≡-prf))))
  ρ-ιth-injective _  ρ ι ρ-inj {x₁ = v₁} {x₂ = v₂} ≡-prf | less m>n | equal refl with ≡-prf
  ... | ()
  ρ-ιth-injective _  ρ ι ρ-inj {x₁ = v₁} {x₂ = v₂} ≡-prf | less m>n | less m>n₁ = m<n-n-pred-injective (ρ-inj (suc-injective ≡-prf))

ρ-SubstDistributivity : {Ty : ℕ → Set} → R.ActionOn Ty → SubstOn Ty → Set
ρ-SubstDistributivity {Ty} ρ-act [_↦_]_ = ∀ {ℓ ℓ'}
                                          → (ρ : Fin ℓ → Fin ℓ')
                                          → (ι : Fin (suc ℓ))
                                          → (ε : STerm ℓ)
                                          → (v : Ty (suc ℓ))
                                          → ρ-act ρ ([ ι ↦ ε ] v) ≡ [ zero ↦ R.act-ε ρ ε ] (ρ-act (ρ-ιth ρ ι) v)

ρ-replace-comm : ∀ (ρ : Fin ℓ → Fin ℓ') ι ε
               → ∀ var → R.act-ε ρ (replace-at ι ε var) ≡ replace-at zero (R.act-ε ρ ε) (ρ-ιth ρ ι var)
ρ-replace-comm ρ ι ε var with ι <>? var
... | less ι<var = refl
... | equal refl = refl
... | greater ι>var = refl

ρ-subst-distr-τ : ρ-SubstDistributivity R.act-τ [_↦τ_]_
ρ-subst-distr-τ ρ ι ε τ
  rewrite ρ-σ-distr-τ ρ (replace-at ι ε) τ
        | σ-ρ-distr-τ (replace-at zero (R.act-ε ρ ε)) (ρ-ιth ρ ι) τ
        | S.act-τ-extensionality (ρ-replace-comm ρ ι ε) τ
        = refl

ρ-subst-distr-ε : ρ-SubstDistributivity R.act-ε [_↦ε_]_
ρ-subst-distr-ε ρ ι ε ε'
  rewrite ρ-σ-distr-ε ρ (replace-at ι ε) ε'
        | σ-ρ-distr-ε (replace-at zero (R.act-ε ρ ε)) (ρ-ιth ρ ι) ε'
        | S.act-ε-extensionality (ρ-replace-comm ρ ι ε) ε'
        = refl

ρ-subst-distr-τ-0 : (ρ : Fin ℓ → Fin ℓ')
                  → (ε : STerm ℓ)
                  → (τ : SType (suc ℓ))
                  → R.act-τ ρ ([ zero ↦τ ε ] τ) ≡ [ zero ↦τ R.act-ε ρ ε ] (R.act-τ (R.ext ρ) τ)
ρ-subst-distr-τ-0 ρ ε τ
  rewrite R.act-τ-extensionality (ρ-0th-is-ext ρ) τ
        = ρ-subst-distr-τ ρ zero ε τ

ρ-subst-distr-ε-0 : (ρ : Fin ℓ → Fin ℓ')
                  → (ε : STerm ℓ)
                  → (ε' : STerm (suc ℓ))
                  → R.act-ε ρ ([ zero ↦ε ε ] ε') ≡ [ zero ↦ε R.act-ε ρ ε ] (R.act-ε (R.ext ρ) ε')
ρ-subst-distr-ε-0 ρ ε ε'
  rewrite R.act-ε-extensionality (ρ-0th-is-ext ρ) ε'
        = ρ-subst-distr-ε ρ zero ε ε'
