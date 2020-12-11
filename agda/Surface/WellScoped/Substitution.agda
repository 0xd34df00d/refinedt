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

ext-replace-comm : ∀ ε (ι : Fin (suc ℓ))
                 → (∀ var-idx → ext (replace-at ι ε) var-idx ≡ replace-at (suc ι) (R.act-ε suc ε) var-idx)
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
                   → (∀ var-idx → ext (replace-at (R.ext ρ ι) (R.act-ε ρ ε)) var-idx ≡ replace-at (suc (R.ext ρ ι)) (R.act-ε (R.ext ρ) (R.act-ε suc ε)) var-idx)
R-ext-replace-comm ε ρ zero zero = refl
R-ext-replace-comm ε ρ (suc ι) zero = refl
R-ext-replace-comm ε ρ zero (suc var-idx) with zero <>? var-idx
... | less m<n rewrite m<n-n-pred-cancel m<n = refl
... | equal refl rewrite R.weaken-ε-comm ρ ε = refl
R-ext-replace-comm ε ρ (suc ι) (suc var-idx) with suc (ρ ι) <>? var-idx
... | less m<n rewrite m<n-n-pred-cancel m<n = refl
... | equal refl rewrite R.weaken-ε-comm ρ ε = refl
... | greater m>n = refl

IdentityUpTo : (Fin ℓ → Fin ℓ') → Fin (suc ℓ) → Set
IdentityUpTo ρ ι = ∀ {n} → (n<ι : n < ι) → toℕ (ρ n) ≡ toℕ n

record CommutingRenamer (ρ : Fin ℓ → Fin ℓ') (ι : Fin (suc ℓ)) : Set where
  field
    ρ-mono : Monotonic ρ
    ρ-id   : IdentityUpTo ρ ι

open CommutingRenamer

ext-monotonic : ∀ {ρ : Fin ℓ → Fin ℓ'}
              → Monotonic ρ
              → Monotonic (R.ext ρ)
ext-monotonic ρ-mono {x = zero} {y = zero} ()
ext-monotonic ρ-mono {x = zero} {y = suc y} (<-zero .y) = <-zero _
ext-monotonic ρ-mono {x = suc x} {y = zero} ()
ext-monotonic ρ-mono {x = suc x} {y = suc y} (<-suc x<y) = <-suc (ρ-mono x<y)

ext-identity : ∀ {ρ : Fin ℓ → Fin ℓ'}
             → IdentityUpTo ρ ι
             → IdentityUpTo (R.ext ρ) (suc ι)
ext-identity ρ-id (<-zero ι) rewrite tighten-zero ι = refl
ext-identity ρ-id (<-suc n<ι) rewrite ρ-id n<ι = refl

ext-commuting : ∀ {ρ : Fin ℓ → Fin ℓ'} {ι}
              → CommutingRenamer ρ ι
              → CommutingRenamer (R.ext ρ) (suc ι)
ext-commuting record { ρ-mono = ρ-mono ; ρ-id = ρ-id } = record { ρ-mono = ext-monotonic ρ-mono
                                                                ; ρ-id = ext-identity ρ-id
                                                                }


RenameSubstDistributivity : {Ty : ℕ → Set} → R.ActionOn Ty → SubstOn Ty → Set
RenameSubstDistributivity {Ty} ρ-act [_↦_]_ = ∀ {ℓ ℓ'}
                                              → (ρ : Fin ℓ → Fin ℓ')
                                              → (ε : STerm ℓ)
                                              → (ι : Fin (suc ℓ))
                                              → (ρ-comm : CommutingRenamer ρ ι)
                                              → (v : Ty (suc ℓ))
                                              → ρ-act ρ ([ ι ↦ ε ] v) ≡ [ R.ext ρ ι ↦ R.act-ε ρ ε ] (ρ-act (R.ext ρ) v)

rename-subst-τ-distr : RenameSubstDistributivity R.act-τ [_↦τ_]_
rename-subst-ρ-distr : RenameSubstDistributivity R.act-ρ [_↦ρ_]_
rename-subst-ε-distr : RenameSubstDistributivity R.act-ε [_↦ε_]_
rename-subst-cons-distr : RenameSubstDistributivity {ADTCons nₐ} R.act-cons [_↦c_]_
rename-subst-branches-distr : RenameSubstDistributivity {CaseBranches nₐ} R.act-branches [_↦bs_]_

rename-subst-τ-distr ρ ε ι ρ-comm ⟨ b ∣ ρ' ⟩ rewrite act-ρ-extensionality (ext-replace-comm ε ι) ρ'
                                                   | act-ρ-extensionality (R-ext-replace-comm ε ρ ι) (R.act-ρ (R.ext (R.ext ρ)) ρ')
                                                   | rename-subst-ρ-distr (R.ext ρ) (R.weaken-ε ε) (suc ι) (ext-commuting ρ-comm) ρ' = refl
rename-subst-τ-distr ρ ε ι ρ-comm (τ₁ ⇒ τ₂) rewrite rename-subst-τ-distr ρ ε ι ρ-comm τ₁
                                                  | act-τ-extensionality (ext-replace-comm ε ι) τ₂
                                                  | act-τ-extensionality (R-ext-replace-comm ε ρ ι) (R.act-τ (R.ext (R.ext ρ)) τ₂)
                                                  | rename-subst-τ-distr (R.ext ρ) (R.weaken-ε ε) (suc ι) (ext-commuting ρ-comm) τ₂ = refl
rename-subst-τ-distr ρ ε ι ρ-comm (⊍ cons) rewrite rename-subst-cons-distr ρ ε ι ρ-comm cons = refl

rename-subst-ρ-distr ρ ε ι ρ-comm (ε₁ ≈ ε₂) rewrite rename-subst-ε-distr ρ ε ι ρ-comm ε₁
                                                  | rename-subst-ε-distr ρ ε ι ρ-comm ε₂ = refl
rename-subst-ρ-distr ρ ε ι ρ-comm (ρ₁ ∧ ρ₂) rewrite rename-subst-ρ-distr ρ ε ι ρ-comm ρ₁
                                                  | rename-subst-ρ-distr ρ ε ι ρ-comm ρ₂ = refl

rename-subst-var-distr-lemma₃ : ∀ (ρ : Fin (suc ℓ) → Fin (suc ℓ')) ι idx (ρ-comm : CommutingRenamer ρ (suc ι))
                              → (ι>idx : ι > idx)
                              → ρ (tighten (<-suc ι>idx)) ≡ tighten (<-suc (ρ-mono ρ-comm ι>idx))
rename-subst-var-distr-lemma₃ ρ ι idx ρ-comm ι>idx = lift-ℕ-≡ sub
  where
    sub : toℕ (ρ (suc (tighten ι>idx))) ≡ suc (toℕ (tighten (ρ-mono ρ-comm ι>idx)))
    sub rewrite ρ-id ρ-comm (<-suc (tighten-preserves-< ι>idx))
              | tighten-is-same-ℕ ι>idx
              | tighten-is-same-ℕ (ρ-mono ρ-comm ι>idx)
              | ρ-id ρ-comm {idx} (<-weaken ι>idx) = refl

ρ-zero≡zero : ∀ (ρ : Fin (suc ℓ) → Fin (suc ℓ')) ι
            → CommutingRenamer ρ (suc ι)
            → ρ zero ≡ zero
ρ-zero≡zero ρ ι record { ρ-mono = _ ; ρ-id = ρ-id } = lift-ℕ-≡ (ρ-id (<-zero ι))

rename-subst-var-distr : ∀ (ρ : Fin ℓ → Fin ℓ') ε (ι : Fin (suc ℓ)) (ρ-comm : CommutingRenamer ρ ι) idx
                       → R.act-ε ρ ([ ι ↦ε ε ] SVar idx) ≡ [ R.ext ρ ι ↦ε R.act-ε ρ ε ] R.act-ε (R.ext ρ) (SVar idx)
rename-subst-var-distr ρ ε zero _ zero = refl
rename-subst-var-distr ρ ε zero _ (suc idx) = refl
rename-subst-var-distr {ℓ' = zero} ρ ε (suc ι) ρ-comm zero = Fin0-elim (ρ ι)
rename-subst-var-distr {ℓ = suc ℓ} {ℓ' = suc ℓ'} ρ ε (suc ι) ρ-comm zero rewrite tighten-zero ι
                                                                               | tighten-zero (ρ ι)
                                                                               | ρ-zero≡zero ρ ι ρ-comm = refl
rename-subst-var-distr {ℓ' = zero} ρ ε (suc ι) ρ-comm (suc idx) = Fin0-elim (ρ ι)
rename-subst-var-distr {ℓ = suc ℓ} {ℓ' = suc ℓ'} ρ ε (suc ι) ρ-comm (suc idx) with ι <>? idx
... | less m<n rewrite <>?-< (ρ-mono ρ-comm m<n) = refl
... | equal refl rewrite <>?-refl-equal (ρ ι) = refl
... | greater m>n rewrite <>?-> (ρ-mono ρ-comm m>n)
                        | rename-subst-var-distr-lemma₃ ρ ι idx ρ-comm m>n = refl

rename-subst-ε-distr ρ ε ι ρ-comm SUnit = refl
rename-subst-ε-distr ρ ε ι ρ-comm (SVar idx) = rename-subst-var-distr ρ ε ι ρ-comm idx
rename-subst-ε-distr ρ ε ι ρ-comm (SLam τ ε') rewrite rename-subst-τ-distr ρ ε ι ρ-comm τ
                                                    | act-ε-extensionality (ext-replace-comm ε ι) ε'
                                                    | act-ε-extensionality (R-ext-replace-comm ε ρ ι) (R.act-ε (R.ext (R.ext ρ)) ε')
                                                    | rename-subst-ε-distr (R.ext ρ) (R.weaken-ε ε) (suc ι) (ext-commuting ρ-comm) ε' = refl
rename-subst-ε-distr ρ ε ι ρ-comm (SApp ε₁ ε₂) rewrite rename-subst-ε-distr ρ ε ι ρ-comm ε₁
                                                     | rename-subst-ε-distr ρ ε ι ρ-comm ε₂ = refl
rename-subst-ε-distr ρ ε ι ρ-comm (SCase ε' branches) rewrite rename-subst-ε-distr ρ ε ι ρ-comm ε'
                                                            | rename-subst-branches-distr ρ ε ι ρ-comm branches = refl
rename-subst-ε-distr ρ ε ι ρ-comm (SCon idx ε' adt-cons) rewrite rename-subst-ε-distr ρ ε ι ρ-comm ε'
                                                               | rename-subst-cons-distr ρ ε ι ρ-comm adt-cons = refl

rename-subst-cons-distr ρ ε ι ρ-comm [] = refl
rename-subst-cons-distr ρ ε ι ρ-comm (τ ∷ τs) rewrite rename-subst-τ-distr ρ ε ι ρ-comm τ
                                                    | rename-subst-cons-distr ρ ε ι ρ-comm τs = refl

rename-subst-branches-distr ρ ε ι ρ-comm [] = refl
rename-subst-branches-distr ρ ε ι ρ-comm (MkCaseBranch body ∷ bs) rewrite act-ε-extensionality (ext-replace-comm ε ι) body
                                                                        | act-ε-extensionality (R-ext-replace-comm ε ρ ι) (R.act-ε (R.ext (R.ext ρ)) body)
                                                                        | rename-subst-ε-distr (R.ext ρ) (R.weaken-ε ε) (suc ι) (ext-commuting ρ-comm) body
                                                                        | rename-subst-branches-distr ρ ε ι ρ-comm bs = refl

rename-subst-τ-distr-0 : (ρ : Fin ℓ → Fin ℓ')
                       → (ε : STerm ℓ)
                       → Monotonic ρ
                       → (τ : SType (suc ℓ))
                       → R.act-τ ρ ([ zero ↦τ ε ] τ) ≡ [ zero ↦τ R.act-ε ρ ε ] (R.act-τ (R.ext ρ) τ)
rename-subst-τ-distr-0 ρ ε ρ-mono τ = rename-subst-τ-distr ρ ε zero (record { ρ-mono = ρ-mono ; ρ-id = λ () }) τ


SubstRenameDistributivity : {Ty : ℕ → Set} → ActionOn Ty → R.ActionOn Ty → Set
SubstRenameDistributivity {Ty} σ-act ρ-act = ∀ {ℓ ℓ'}
                                             → (σ : Fin ℓ' → STerm ℓ)
                                             → (ρ : Fin ℓ → Fin ℓ')
                                             → (v : Ty ℓ)
                                             → σ-act σ (ρ-act ρ v) ≡ σ-act (σ ∘ ρ) v

ext-Rext-distr : (σ : Fin ℓ' → STerm ℓ)
               → (ρ : Fin ℓ → Fin ℓ')
               → (∀ x → ext σ (R.ext ρ x) ≡ ext (σ ∘ ρ) x)
ext-Rext-distr σ ρ zero = refl
ext-Rext-distr σ ρ (suc x) = refl

subst-rename-τ-distr : SubstRenameDistributivity act-τ R.act-τ
subst-rename-ρ-distr : SubstRenameDistributivity act-ρ R.act-ρ
subst-rename-ε-distr : SubstRenameDistributivity act-ε R.act-ε
subst-rename-cons-distr : SubstRenameDistributivity {ADTCons nₐ} act-cons R.act-cons
subst-rename-branches-distr : SubstRenameDistributivity {CaseBranches nₐ} act-branches R.act-branches

subst-rename-τ-distr σ ρ ⟨ b ∣ ρ' ⟩ rewrite subst-rename-ρ-distr (ext σ) (R.ext ρ) ρ'
                                          | act-ρ-extensionality (ext-Rext-distr σ ρ) ρ' = refl
subst-rename-τ-distr σ ρ (τ₁ ⇒ τ₂) rewrite subst-rename-τ-distr σ ρ τ₁
                                         | subst-rename-τ-distr (ext σ) (R.ext ρ) τ₂
                                         | act-τ-extensionality (ext-Rext-distr σ ρ) τ₂ = refl
subst-rename-τ-distr σ ρ (⊍ cons) rewrite subst-rename-cons-distr σ ρ cons = refl

subst-rename-ρ-distr σ ρ (ε₁ ≈ ε₂) rewrite subst-rename-ε-distr σ ρ ε₁
                                         | subst-rename-ε-distr σ ρ ε₂ = refl
subst-rename-ρ-distr σ ρ (ρ₁ ∧ ρ₂) rewrite subst-rename-ρ-distr σ ρ ρ₁
                                         | subst-rename-ρ-distr σ ρ ρ₂ = refl

subst-rename-ε-distr σ ρ SUnit = refl
subst-rename-ε-distr σ ρ (SVar idx) = refl
subst-rename-ε-distr σ ρ (SLam τ ε) rewrite subst-rename-τ-distr σ ρ τ
                                          | subst-rename-ε-distr (ext σ) (R.ext ρ) ε
                                          | act-ε-extensionality (ext-Rext-distr σ ρ) ε = refl
subst-rename-ε-distr σ ρ (SApp ε₁ ε₂) rewrite subst-rename-ε-distr σ ρ ε₁
                                            | subst-rename-ε-distr σ ρ ε₂ = refl
subst-rename-ε-distr σ ρ (SCase ε branches) rewrite subst-rename-ε-distr σ ρ ε
                                                  | subst-rename-branches-distr σ ρ branches = refl
subst-rename-ε-distr σ ρ (SCon idx ε cons) rewrite subst-rename-ε-distr σ ρ ε
                                                 | subst-rename-cons-distr σ ρ cons = refl

subst-rename-cons-distr σ ρ [] = refl
subst-rename-cons-distr σ ρ (τ ∷ cons) rewrite subst-rename-τ-distr σ ρ τ
                                             | subst-rename-cons-distr σ ρ cons = refl

subst-rename-branches-distr σ ρ [] = refl
subst-rename-branches-distr σ ρ (MkCaseBranch ε ∷ bs) rewrite subst-rename-ε-distr (ext σ) (R.ext ρ) ε
                                                            | subst-rename-branches-distr σ ρ bs
                                                            | act-ε-extensionality (ext-Rext-distr σ ρ) ε = refl


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
