{-# OPTIONS --safe #-}

module Surface.WellScoped.Substitution.Distributivity where

open import Data.Fin using (Fin; suc; zero; raise; toℕ)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Vec
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Fin.Extra
open import Surface.WellScoped
open import Surface.WellScoped.Substitution as S
import Surface.WellScoped.Renaming as R

ρ-σ-Distributivity : {Ty : ℕ → Set} → R.ActionOn Ty → ActionOn Ty → Set
ρ-σ-Distributivity {Ty} ρ-act σ-act = ∀ {ℓ₀ ℓ₁ ℓ₂}
                                      → (ρ : Fin ℓ₁ → Fin ℓ₂)
                                      → (σ : Fin ℓ₀ → STerm ℓ₁)
                                      → (v : Ty ℓ₀)
                                      → ρ-act ρ (σ-act σ v) ≡ σ-act (R.act-ε ρ ∘ σ) v

ρ-σ-distr-τ : ρ-σ-Distributivity R.act-τ act-τ
ρ-σ-distr-ρ : ρ-σ-Distributivity R.act-ρ act-ρ
ρ-σ-distr-ε : ρ-σ-Distributivity R.act-ε act-ε
ρ-σ-distr-cons : ρ-σ-Distributivity {ADTCons nₐ} R.act-cons act-cons
ρ-σ-distr-branches : ρ-σ-Distributivity {CaseBranches nₐ} R.act-branches act-branches

R-ext-ext-commutes-ε : (ρ : Fin ℓ₁ → Fin ℓ₂)
                     → (σ : Fin ℓ₀ → STerm ℓ₁)
                     → ∀ x → R.act-ε (R.ext ρ) (ext σ x) ≡ ext (R.act-ε ρ ∘ σ) x
R-ext-ext-commutes-ε ρ σ zero = refl
R-ext-ext-commutes-ε ρ σ (suc x) rewrite R.act-ε-distr suc (R.ext ρ) (σ x)
                                       | R.act-ε-distr ρ suc (σ x)
                                       = refl

ρ-σ-distr-τ ρ σ ⟨ b ∣ ρ' ⟩ rewrite ρ-σ-distr-ρ (R.ext ρ) (ext σ) ρ'
                                 | act-ρ-extensionality (R-ext-ext-commutes-ε ρ σ) ρ'
                                 = refl
ρ-σ-distr-τ ρ σ (τ₁ ⇒ τ₂) rewrite ρ-σ-distr-τ ρ σ τ₁
                                | ρ-σ-distr-τ (R.ext ρ) (ext σ) τ₂
                                | act-τ-extensionality (R-ext-ext-commutes-ε ρ σ) τ₂
                                = refl
ρ-σ-distr-τ ρ σ (⊍ cons) rewrite ρ-σ-distr-cons ρ σ cons = refl

ρ-σ-distr-ρ ρ σ (ε₁ ≈ ε₂) rewrite ρ-σ-distr-ε ρ σ ε₁
                                | ρ-σ-distr-ε ρ σ ε₂
                                = refl
ρ-σ-distr-ρ ρ σ (ρ₁ ∧ ρ₂) rewrite ρ-σ-distr-ρ ρ σ ρ₁
                                | ρ-σ-distr-ρ ρ σ ρ₂
                                = refl

ρ-σ-distr-ε ρ σ SUnit = refl
ρ-σ-distr-ε ρ σ (SVar idx) = refl
ρ-σ-distr-ε ρ σ (SLam τ ε) rewrite ρ-σ-distr-τ ρ σ τ
                                 | ρ-σ-distr-ε (R.ext ρ) (ext σ) ε
                                 | act-ε-extensionality (R-ext-ext-commutes-ε ρ σ) ε
                                 = refl
ρ-σ-distr-ε ρ σ (SApp ε₁ ε₂) rewrite ρ-σ-distr-ε ρ σ ε₁
                                   | ρ-σ-distr-ε ρ σ ε₂
                                   = refl
ρ-σ-distr-ε ρ σ (SCase ε branches) rewrite ρ-σ-distr-ε ρ σ ε
                                         | ρ-σ-distr-branches ρ σ branches
                                         = refl
ρ-σ-distr-ε ρ σ (SCon idx ε cons) rewrite ρ-σ-distr-ε ρ σ ε
                                        | ρ-σ-distr-cons ρ σ cons
                                        = refl

ρ-σ-distr-cons ρ σ [] = refl
ρ-σ-distr-cons ρ σ (τ ∷ cons) rewrite ρ-σ-distr-τ ρ σ τ
                                    | ρ-σ-distr-cons ρ σ cons
                                    = refl

ρ-σ-distr-branches ρ σ [] = refl
ρ-σ-distr-branches ρ σ (MkCaseBranch ε ∷ bs) rewrite ρ-σ-distr-ε (R.ext ρ) (ext σ) ε
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

σ-ρ-distr-τ : σ-ρ-Distributivity act-τ R.act-τ
σ-ρ-distr-ρ : σ-ρ-Distributivity act-ρ R.act-ρ
σ-ρ-distr-ε : σ-ρ-Distributivity act-ε R.act-ε
σ-ρ-distr-cons : σ-ρ-Distributivity {ADTCons nₐ} act-cons R.act-cons
σ-ρ-distr-branches : σ-ρ-Distributivity {CaseBranches nₐ} act-branches R.act-branches

σ-ρ-distr-τ σ ρ ⟨ b ∣ ρ' ⟩ rewrite σ-ρ-distr-ρ (ext σ) (R.ext ρ) ρ'
                                 | act-ρ-extensionality (ext-Rext-distr σ ρ) ρ'
                                 = refl
σ-ρ-distr-τ σ ρ (τ₁ ⇒ τ₂) rewrite σ-ρ-distr-τ σ ρ τ₁
                                | σ-ρ-distr-τ (ext σ) (R.ext ρ) τ₂
                                | act-τ-extensionality (ext-Rext-distr σ ρ) τ₂
                                = refl
σ-ρ-distr-τ σ ρ (⊍ cons) rewrite σ-ρ-distr-cons σ ρ cons = refl

σ-ρ-distr-ρ σ ρ (ε₁ ≈ ε₂) rewrite σ-ρ-distr-ε σ ρ ε₁
                                | σ-ρ-distr-ε σ ρ ε₂
                                = refl
σ-ρ-distr-ρ σ ρ (ρ₁ ∧ ρ₂) rewrite σ-ρ-distr-ρ σ ρ ρ₁
                                | σ-ρ-distr-ρ σ ρ ρ₂
                                = refl

σ-ρ-distr-ε σ ρ SUnit = refl
σ-ρ-distr-ε σ ρ (SVar idx) = refl
σ-ρ-distr-ε σ ρ (SLam τ ε) rewrite σ-ρ-distr-τ σ ρ τ
                                 | σ-ρ-distr-ε (ext σ) (R.ext ρ) ε
                                 | act-ε-extensionality (ext-Rext-distr σ ρ) ε
                                 = refl
σ-ρ-distr-ε σ ρ (SApp ε₁ ε₂) rewrite σ-ρ-distr-ε σ ρ ε₁
                                   | σ-ρ-distr-ε σ ρ ε₂
                                   = refl
σ-ρ-distr-ε σ ρ (SCase ε branches) rewrite σ-ρ-distr-ε σ ρ ε
                                         | σ-ρ-distr-branches σ ρ branches
                                         = refl
σ-ρ-distr-ε σ ρ (SCon idx ε cons) rewrite σ-ρ-distr-ε σ ρ ε
                                        | σ-ρ-distr-cons σ ρ cons
                                        = refl

σ-ρ-distr-cons σ ρ [] = refl
σ-ρ-distr-cons σ ρ (τ ∷ cons) rewrite σ-ρ-distr-τ σ ρ τ
                                    | σ-ρ-distr-cons σ ρ cons
                                    = refl

σ-ρ-distr-branches σ ρ [] = refl
σ-ρ-distr-branches σ ρ (MkCaseBranch ε ∷ bs) rewrite σ-ρ-distr-ε (ext σ) (R.ext ρ) ε
                                                   | σ-ρ-distr-branches σ ρ bs
                                                   | act-ε-extensionality (ext-Rext-distr σ ρ) ε
                                                   = refl


act-ε-ext-distr : (σ₁ : Fin ℓ₀ → STerm ℓ₁)
                → (σ₂ : Fin ℓ₁ → STerm ℓ₂)
                → (x : Fin (suc ℓ₀))
                → act-ε (ext σ₂) (ext σ₁ x) ≡ ext (act-ε σ₂ ∘ σ₁) x
act-ε-ext-distr σ₁ σ₂ zero = refl
act-ε-ext-distr σ₁ σ₂ (suc x) rewrite σ-ρ-distr-ε (ext σ₂) suc (σ₁ x)
                                    | ρ-σ-distr-ε suc σ₂ (σ₁ x)
                                    = refl

ActDistributivity : {Ty : ℕ → Set} → ActionOn Ty → Set
ActDistributivity {Ty} act = ∀ {ℓ₀ ℓ₁ ℓ₂}
                             → (σ₁ : Fin ℓ₀ → STerm ℓ₁)
                             → (σ₂ : Fin ℓ₁ → STerm ℓ₂)
                             → (v : Ty ℓ₀)
                             → act σ₂ (act σ₁ v) ≡ act (act-ε σ₂ ∘ σ₁) v

act-τ-distr : ActDistributivity act-τ
act-ρ-distr : ActDistributivity act-ρ
act-ε-distr : ActDistributivity act-ε
act-cons-distr : ActDistributivity {ADTCons nₐ} act-cons
act-branches-distr : ActDistributivity {CaseBranches nₐ} act-branches

act-τ-distr σ₁ σ₂ ⟨ b ∣ ρ ⟩ rewrite act-ρ-distr (ext σ₁) (ext σ₂) ρ
                                  | act-ρ-extensionality (act-ε-ext-distr σ₁ σ₂) ρ
                                  = refl
act-τ-distr σ₁ σ₂ (τ₁ ⇒ τ₂) rewrite act-τ-distr σ₁ σ₂ τ₁
                                  | act-τ-distr (ext σ₁) (ext σ₂) τ₂
                                  | act-τ-extensionality (act-ε-ext-distr σ₁ σ₂) τ₂
                                  = refl
act-τ-distr σ₁ σ₂ (⊍ cons) rewrite act-cons-distr σ₁ σ₂ cons = refl

act-ρ-distr σ₁ σ₂ (ε₁ ≈ ε₂) rewrite act-ε-distr σ₁ σ₂ ε₁
                                  | act-ε-distr σ₁ σ₂ ε₂
                                  = refl
act-ρ-distr σ₁ σ₂ (ρ₁ ∧ ρ₂) rewrite act-ρ-distr σ₁ σ₂ ρ₁
                                  | act-ρ-distr σ₁ σ₂ ρ₂
                                  = refl

act-ε-distr σ₁ σ₂ SUnit = refl
act-ε-distr σ₁ σ₂ (SVar idx) = refl
act-ε-distr σ₁ σ₂ (SLam τ ε) rewrite act-τ-distr σ₁ σ₂ τ
                                   | act-ε-distr (ext σ₁) (ext σ₂) ε
                                   | act-ε-extensionality (act-ε-ext-distr σ₁ σ₂) ε
                                   = refl
act-ε-distr σ₁ σ₂ (SApp ε₁ ε₂) rewrite act-ε-distr σ₁ σ₂ ε₁
                                     | act-ε-distr σ₁ σ₂ ε₂
                                     = refl
act-ε-distr σ₁ σ₂ (SCase ε branches) rewrite act-ε-distr σ₁ σ₂ ε
                                           | act-branches-distr σ₁ σ₂ branches
                                           = refl
act-ε-distr σ₁ σ₂ (SCon idx ε cons) rewrite act-ε-distr σ₁ σ₂ ε
                                          | act-cons-distr σ₁ σ₂ cons
                                          = refl

act-cons-distr σ₁ σ₂ [] = refl
act-cons-distr σ₁ σ₂ (τ ∷ cons) rewrite act-τ-distr σ₁ σ₂ τ
                                      | act-cons-distr σ₁ σ₂ cons
                                      = refl

act-branches-distr σ₁ σ₂ [] = refl
act-branches-distr σ₁ σ₂ (MkCaseBranch ε ∷ bs) rewrite act-ε-distr (ext σ₁) (ext σ₂) ε
                                                     | act-ε-extensionality (act-ε-ext-distr σ₁ σ₂) ε
                                                     | act-branches-distr σ₁ σ₂ bs
                                                     = refl


IdentityUpTo : (Fin ℓ → Fin ℓ') → Fin (suc ℓ) → Set
IdentityUpTo ρ ι = ∀ {n} → (n<ι : n < ι) → toℕ (ρ n) ≡ toℕ n

record CommutingRenamer (ρ : Fin ℓ → Fin ℓ') (ι : Fin (suc ℓ)) : Set where
  field
    ρ-mono : Monotonic ρ
    ρ-id   : IdentityUpTo ρ ι

open CommutingRenamer

ext-identity : ∀ {ρ : Fin ℓ → Fin ℓ'}
             → IdentityUpTo ρ ι
             → IdentityUpTo (R.ext ρ) (suc ι)
ext-identity ρ-id (<-zero ι) rewrite tighten-zero ι = refl
ext-identity ρ-id (<-suc n<ι) rewrite ρ-id n<ι = refl

ext-commuting : ∀ {ρ : Fin ℓ → Fin ℓ'} {ι}
              → CommutingRenamer ρ ι
              → CommutingRenamer (R.ext ρ) (suc ι)
ext-commuting record { ρ-mono = ρ-mono ; ρ-id = ρ-id } = record { ρ-mono = R.ext-monotonic ρ-mono
                                                                ; ρ-id = ext-identity ρ-id
                                                                }

ρ-SubstDistributivity : {Ty : ℕ → Set} → R.ActionOn Ty → SubstOn Ty → Set
ρ-SubstDistributivity {Ty} ρ-act [_↦_]_ = ∀ {ℓ ℓ'}
                                          → (ρ : Fin ℓ → Fin ℓ')
                                          → (ι : Fin (suc ℓ))
                                          → (ρ-comm : CommutingRenamer ρ ι)
                                          → (ε : STerm ℓ)
                                          → (v : Ty (suc ℓ))
                                          → ρ-act ρ ([ ι ↦ ε ] v) ≡ [ R.ext ρ ι ↦ R.act-ε ρ ε ] (ρ-act (R.ext ρ) v)

ρ-<-pred-comm : ∀ {ρ : Fin ℓ → Fin ℓ'} {ι} {var}
              → (ρ-mono : Monotonic ρ)
              → (ι<var : ι < var)
              → ρ (m<n-n-pred ι<var) ≡ m<n-n-pred (R.ext-monotonic ρ-mono ι<var)
ρ-<-pred-comm {var = suc var} ρ-mono ι<var = refl

ρ->-tighten-comm : ∀ {ι}
                 → (ρ : Fin ℓ → Fin ℓ')
                 → (ρ-comm : CommutingRenamer ρ ι)
                 → (let ρ-mono = CommutingRenamer.ρ-mono ρ-comm)
                 → (var : _)
                 → (ι>var : ι > var)
                 → ρ (tighten ι>var) ≡ tighten (R.ext-monotonic ρ-mono ι>var)
ρ->-tighten-comm {ℓ = zero} _ _ _ (<-zero n) = Fin0-elim n
ρ->-tighten-comm {ℓ' = zero} ρ _ _ (<-zero n) = Fin0-elim (ρ n)
ρ->-tighten-comm {ℓ = suc ℓ} {ℓ' = suc ℓ'} ρ ρ-comm zero (<-zero n) = lift-ℕ-≡ (CommutingRenamer.ρ-id ρ-comm (<-zero n))
ρ->-tighten-comm {ℓ = suc ℓ} ρ ρ-comm (suc var) (<-suc ι>var) = lift-ℕ-≡ (
  begin
    toℕ (ρ (suc (tighten ι>var)))
  ≡⟨ CommutingRenamer.ρ-id ρ-comm (suc-tighten ι>var) ⟩
    suc (toℕ (tighten ι>var))
  ≡⟨ cong suc (tighten-is-same-ℕ ι>var) ⟩
    suc (toℕ var)
  ≡⟨ cong suc (sym (CommutingRenamer.ρ-id ρ-comm (<-weaken ι>var))) ⟩
    suc (toℕ (ρ var))
  ≡⟨ sym (tighten-is-same-ℕ (<-suc (CommutingRenamer.ρ-mono ρ-comm ι>var))) ⟩
    toℕ (tighten (<-suc (CommutingRenamer.ρ-mono ρ-comm ι>var)))
  ∎
  )

ρ-replace-comm : ∀ (ρ : Fin ℓ → Fin ℓ') ι ε
               → CommutingRenamer ρ ι
               → ∀ var → R.act-ε ρ (replace-at ι ε var) ≡ replace-at (R.ext ρ ι) (R.act-ε ρ ε) (R.ext ρ var)
ρ-replace-comm ρ ι ε ρ-comm var with ι <>? var
... | less ι<var rewrite <>?-< (R.ext-monotonic (CommutingRenamer.ρ-mono ρ-comm) ι<var)
                       | ρ-<-pred-comm (CommutingRenamer.ρ-mono ρ-comm) ι<var
                       = refl
... | equal refl rewrite <>?-refl-equal (R.ext ρ ι) = refl
... | greater ι>var rewrite <>?-> (R.ext-monotonic (CommutingRenamer.ρ-mono ρ-comm) ι>var)
                          | ρ->-tighten-comm ρ ρ-comm var ι>var
                          = refl

ρ-subst-distr-τ : ρ-SubstDistributivity R.act-τ [_↦τ_]_
ρ-subst-distr-τ ρ ι ρ-comm ε τ rewrite ρ-σ-distr-τ ρ (replace-at ι ε) τ
                                     | σ-ρ-distr-τ (replace-at (R.ext ρ ι) (R.act-ε ρ ε)) (R.ext ρ) τ
                                     | S.act-τ-extensionality (ρ-replace-comm ρ ι ε ρ-comm) τ
                                     = refl

ρ-subst-distr-ε : ρ-SubstDistributivity R.act-ε [_↦ε_]_
ρ-subst-distr-ε ρ ι ρ-comm ε ε' rewrite ρ-σ-distr-ε ρ (replace-at ι ε) ε'
                                      | σ-ρ-distr-ε (replace-at (R.ext ρ ι) (R.act-ε ρ ε)) (R.ext ρ) ε'
                                      | S.act-ε-extensionality (ρ-replace-comm ρ ι ε ρ-comm) ε'
                                      = refl

ρ-subst-distr-τ-0 : (ρ : Fin ℓ → Fin ℓ')
                  → Monotonic ρ
                  → (ε : STerm ℓ)
                  → (τ : SType (suc ℓ))
                  → R.act-τ ρ ([ zero ↦τ ε ] τ) ≡ [ zero ↦τ R.act-ε ρ ε ] (R.act-τ (R.ext ρ) τ)
ρ-subst-distr-τ-0 ρ ρ-mono = ρ-subst-distr-τ ρ zero (record { ρ-mono = ρ-mono ; ρ-id = λ () })

ρ-subst-distr-ε-0 : (ρ : Fin ℓ → Fin ℓ')
                  → Monotonic ρ
                  → (ε : STerm ℓ)
                  → (ε' : STerm (suc ℓ))
                  → R.act-ε ρ ([ zero ↦ε ε ] ε') ≡ [ zero ↦ε R.act-ε ρ ε ] (R.act-ε (R.ext ρ) ε')
ρ-subst-distr-ε-0 ρ ρ-mono = ρ-subst-distr-ε ρ zero (record { ρ-mono = ρ-mono ; ρ-id = λ () })
