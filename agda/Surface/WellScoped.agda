{-# OPTIONS --safe #-}

module Surface.WellScoped where

open import Agda.Builtin.Bool
open import Agda.Builtin.List public
open import Agda.Builtin.String

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin public using (Fin; suc; zero)
open import Data.Fin.Extra
open import Data.Nat public using (ℕ; suc; zero)
open import Data.Vec
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

data BaseType : Set where
  BUnit : BaseType

record ℕₐ : Set where
  constructor Mkℕₐ
  field
    get-length : ℕ

variable
  n ℓ ℓ' ℓ₀ ℓ₁ ℓ₂ : ℕ
  nₐ : ℕₐ
  b b' b₁ b₂ : BaseType
  idx ι : Fin ℓ

data SType (ℓ : ℕ) : Set
data STerm (ℓ : ℕ) : Set
data Refinement (ℓ : ℕ) : Set

ADTCons : ℕₐ → ℕ → Set
ADTCons (Mkℕₐ n) ℓ = Vec (SType ℓ) n

record CaseBranch (ℓ : ℕ) : Set where
  constructor MkCaseBranch
  inductive
  field
    body : STerm (suc ℓ)

CaseBranches : ℕₐ → ℕ → Set
CaseBranches (Mkℕₐ n) ℓ = Vec (CaseBranch ℓ) n

data SType ℓ where
  ⟨_∣_⟩ : (b : BaseType)
        → (ρ : Refinement (suc ℓ))
        → SType ℓ
  _⇒_   : (τ₁ : SType ℓ)
        → (τ₂ : SType (suc ℓ))
        → SType ℓ
  ⊍_    : (cons : ADTCons (Mkℕₐ (suc n)) ℓ)
        → SType ℓ

-- NOTE having `SType ℓ` instead of `SType (suc ℓ)` in SLam's type prevents the type from referring the argument itself,
-- which kinda breaks T-Exact and similar rules from the refinement reflection paper,
-- but now I'm not sure if agreement holds for the type system in that paper.
data STerm ℓ where
  SUnit : STerm ℓ
  SVar  : (idx : Fin ℓ)
        → STerm ℓ
  SLam  : (τ : SType ℓ)
        → (ε : STerm (suc ℓ))
        → STerm ℓ
  SApp  : (ε₁ ε₂ : STerm ℓ)
        → STerm ℓ
  SCase : (scrut : STerm ℓ)
        → (branches : CaseBranches nₐ ℓ)
        → STerm ℓ
  SCon  : (idx : Fin n)
        → (body : STerm ℓ)
        → (adt-cons : ADTCons (Mkℕₐ n) ℓ)
        → STerm ℓ

data Refinement ℓ where
  _≈_ : (ε₁ ε₂ : STerm ℓ) → Refinement ℓ
  _∧_ : (ρ₁ ρ₂ : Refinement ℓ) → Refinement ℓ


infixl 5 _,_
data Ctx : ℕ → Set where
  ⊘   : Ctx 0
  _,_ : Ctx ℓ → SType ℓ → Ctx (suc ℓ)

variable
  Γ Γ' Δ : Ctx ℓ
  τ τ' τ₁ τ₂ τ₁' τ₂' τᵢ τⱼ : SType ℓ
  ε ε' ε₁ ε₂ : STerm ℓ
  ρ₁ ρ₂ : Refinement ℓ

Τ : Refinement ℓ
Τ = SUnit ≈ SUnit

record VarAction : Set₁ where
  field
    Target : ℕ → Set
    var-action : (Fin ℓ → Target ℓ')
               → (Fin ℓ → STerm ℓ')
    ext : (Fin ℓ → Target ℓ')
        → (Fin (suc ℓ) → Target (suc ℓ'))

module ActionScoped (α : VarAction) where
  open VarAction α public

  var-action-record : VarAction
  var-action-record = α

  ActionOn : (ℕ → Set) → Set
  ActionOn Ty = ∀ {ℓ ℓ'} → (Fin ℓ → Target ℓ') → Ty ℓ → Ty ℓ'

  act-ρ : ActionOn Refinement
  act-τ : ActionOn SType
  act-ε : ActionOn STerm
  act-cons : ActionOn (ADTCons nₐ)
  act-branches : ActionOn (CaseBranches nₐ)

  act-ρ f (ε₁ ≈ ε₂) = act-ε f ε₁ ≈ act-ε f ε₂
  act-ρ f (ρ₁ ∧ ρ₂) = act-ρ f ρ₁ ∧ act-ρ f ρ₂

  act-τ f ⟨ b ∣ ρ ⟩ = ⟨ b ∣ act-ρ (ext f) ρ ⟩
  act-τ f (τ₁ ⇒ τ₂) = act-τ f τ₁ ⇒ act-τ (ext f) τ₂
  act-τ f (⊍ cons)  = ⊍ (act-cons f cons)

  act-cons _ [] = []
  act-cons f (τ ∷ τs) = act-τ f τ ∷ act-cons f τs

  act-branches _ [] = []
  act-branches f (MkCaseBranch body ∷ bs) = MkCaseBranch (act-ε (ext f) body) ∷ act-branches f bs

  act-ε f SUnit = SUnit
  act-ε f (SVar idx) = var-action f idx
  act-ε f (SLam τ ε) = SLam (act-τ f τ) (act-ε (ext f) ε)
  act-ε f (SApp ε₁ ε₂) = SApp (act-ε f ε₁) (act-ε f ε₂)
  act-ε f (SCase scrut branches) = SCase (act-ε f scrut) (act-branches f branches)
  act-ε f (SCon idx body adt-cons) = SCon idx (act-ε f body) (act-cons f adt-cons)

record VarActionProps (act : VarAction) : Set where
  open VarAction act
  field
    ≡-ext : {f₁ f₂ : Fin ℓ → Target ℓ'}
          → (∀ x → f₁ x ≡ f₂ x)
          → (∀ x → ext f₁ x ≡ ext f₂ x)
    var-action-cong : {f₁ f₂ : Fin ℓ → Target ℓ'}
                    → (∀ x → f₁ x ≡ f₂ x)
                    → (∀ x → var-action f₁ x ≡ var-action f₂ x)

module ActionScopedLemmas (act : VarAction) (props : VarActionProps act) where
  open ActionScoped act
  open VarActionProps props

  ActExtensionality : {Ty : ℕ → Set} → ActionOn Ty → Set
  ActExtensionality {Ty} act = ∀ {ℓ ℓ'}
                               → {f₁ f₂ : Fin ℓ → Target ℓ'}
                               → ((x : Fin ℓ) → f₁ x ≡ f₂ x)
                               → (v : Ty ℓ)
                               → act f₁ v ≡ act f₂ v

  act-τ-extensionality : ActExtensionality act-τ
  act-ρ-extensionality : ActExtensionality act-ρ
  act-ε-extensionality : ActExtensionality act-ε
  act-cons-extensionality : ActExtensionality {ADTCons nₐ} act-cons
  act-branches-extensionality : ActExtensionality {CaseBranches nₐ} act-branches

  act-τ-extensionality x-≡ ⟨ b ∣ ρ ⟩ rewrite act-ρ-extensionality (≡-ext x-≡) ρ = refl
  act-τ-extensionality x-≡ (τ₁ ⇒ τ₂) rewrite act-τ-extensionality x-≡ τ₁
                                           | act-τ-extensionality (≡-ext x-≡) τ₂ = refl
  act-τ-extensionality x-≡ (⊍ cons) rewrite act-cons-extensionality x-≡ cons = refl

  act-ρ-extensionality x-≡ (ε₁ ≈ ε₂) rewrite act-ε-extensionality x-≡ ε₁
                                           | act-ε-extensionality x-≡ ε₂ = refl
  act-ρ-extensionality x-≡ (ρ₁ ∧ ρ₂) rewrite act-ρ-extensionality x-≡ ρ₁
                                           | act-ρ-extensionality x-≡ ρ₂ = refl

  act-ε-extensionality x-≡ SUnit = refl
  act-ε-extensionality x-≡ (SVar idx) rewrite var-action-cong x-≡ idx = refl
  act-ε-extensionality x-≡ (SLam τ ε) rewrite act-τ-extensionality x-≡ τ
                                            | act-ε-extensionality (≡-ext x-≡) ε = refl
  act-ε-extensionality x-≡ (SApp ε₁ ε₂) rewrite act-ε-extensionality x-≡ ε₁
                                              | act-ε-extensionality x-≡ ε₂ = refl
  act-ε-extensionality x-≡ (SCase ε branches) rewrite act-ε-extensionality x-≡ ε
                                                    | act-branches-extensionality x-≡ branches = refl
  act-ε-extensionality x-≡ (SCon idx ε cons) rewrite act-ε-extensionality x-≡ ε
                                                   | act-cons-extensionality x-≡ cons = refl

  act-cons-extensionality x-≡ [] = refl
  act-cons-extensionality x-≡ (τ ∷ τs) rewrite act-τ-extensionality x-≡ τ
                                             | act-cons-extensionality x-≡ τs = refl

  act-branches-extensionality x-≡ [] = refl
  act-branches-extensionality x-≡ (MkCaseBranch body ∷ bs) rewrite act-ε-extensionality (≡-ext x-≡) body
                                                                 | act-branches-extensionality x-≡ bs = refl

module R where
  open ActionScoped (record { Target = Fin
                            ; var-action = λ r idx → SVar (r idx)
                            ; ext = λ where _ zero → zero
                                            r (suc n) → suc (r n)
                            }
                    ) public

  weaken-τ : SType ℓ → SType (suc ℓ)
  weaken-τ = act-τ suc

  weaken-ε : STerm ℓ → STerm (suc ℓ)
  weaken-ε = act-ε suc


  ≡-ext : {f₁ f₂ : Fin ℓ → Fin ℓ'}
        → (∀ x → f₁ x ≡ f₂ x)
        → (∀ x → ext f₁ x ≡ ext f₂ x)
  ≡-ext _ zero = refl
  ≡-ext x-≡ (suc x) rewrite x-≡ x = refl

  var-action-cong : {f₁ f₂ : Fin ℓ → Fin ℓ'}
                  → (∀ x → f₁ x ≡ f₂ x)
                  → (∀ x → var-action f₁ x ≡ var-action f₂ x)
  var-action-cong x-≡ x rewrite x-≡ x = refl

  open ActionScopedLemmas var-action-record
                          record { ≡-ext = ≡-ext
                                 ; var-action-cong = var-action-cong
                                 }
                          public

  ext-distr : (r₁ : Fin ℓ₀ → Fin ℓ₁)
            → (r₂ : Fin ℓ₁ → Fin ℓ₂)
            → ∀ x
            → ext r₂ (ext r₁ x) ≡ ext (λ x → r₂ (r₁ x)) x
  ext-distr _ _ zero = refl
  ext-distr _ _ (suc x) = refl

  ActDistributivity : {Ty : ℕ → Set} → ActionOn Ty → Set
  ActDistributivity {Ty} act = ∀ {ℓ₀ ℓ₁ ℓ₂}
                               → (r₁ : Fin ℓ₀ → Fin ℓ₁)
                               → (r₂ : Fin ℓ₁ → Fin ℓ₂)
                               → (v : Ty ℓ₀)
                               → act r₂ (act r₁ v) ≡ act (r₂ ∘ r₁) v

  act-τ-distr : ActDistributivity act-τ
  act-ρ-distr : ActDistributivity act-ρ
  act-ε-distr : ActDistributivity act-ε
  act-cons-distr : ActDistributivity {ADTCons nₐ} act-cons
  act-branches-distr : ActDistributivity {CaseBranches nₐ} act-branches

  act-τ-distr r₁ r₂ ⟨ b ∣ ρ ⟩ rewrite act-ρ-distr (ext r₁) (ext r₂) ρ
                                    | act-ρ-extensionality (ext-distr r₁ r₂) ρ = refl
  act-τ-distr r₁ r₂ (τ₁ ⇒ τ₂) rewrite act-τ-distr r₁ r₂ τ₁
                                    | act-τ-distr (ext r₁) (ext r₂) τ₂
                                    | act-τ-extensionality (ext-distr r₁ r₂) τ₂ = refl
  act-τ-distr r₁ r₂ (⊍ cons) rewrite act-cons-distr r₁ r₂ cons = refl

  act-ρ-distr r₁ r₂ (ε₁ ≈ ε₂) rewrite act-ε-distr r₁ r₂ ε₁
                                    | act-ε-distr r₁ r₂ ε₂ = refl
  act-ρ-distr r₁ r₂ (ρ₁ ∧ ρ₂) rewrite act-ρ-distr r₁ r₂ ρ₁
                                    | act-ρ-distr r₁ r₂ ρ₂ = refl

  act-ε-distr r₁ r₂ SUnit = refl
  act-ε-distr r₁ r₂ (SVar idx) = refl
  act-ε-distr r₁ r₂ (SLam τ ε) rewrite act-τ-distr r₁ r₂ τ
                                     | act-ε-distr (ext r₁) (ext r₂) ε
                                     | act-ε-extensionality (ext-distr r₁ r₂) ε = refl
  act-ε-distr r₁ r₂ (SApp ε₁ ε₂) rewrite act-ε-distr r₁ r₂ ε₁
                                       | act-ε-distr r₁ r₂ ε₂ = refl
  act-ε-distr r₁ r₂ (SCase ε branches) rewrite act-ε-distr r₁ r₂ ε
                                             | act-branches-distr r₁ r₂ branches = refl
  act-ε-distr r₁ r₂ (SCon idx ε cons) rewrite act-ε-distr r₁ r₂ ε
                                            | act-cons-distr r₁ r₂ cons = refl

  act-cons-distr r₁ r₂ [] = refl
  act-cons-distr r₁ r₂ (τ ∷ τs) rewrite act-τ-distr r₁ r₂ τ
                                      | act-cons-distr r₁ r₂ τs = refl

  act-branches-distr r₁ r₂ [] = refl
  act-branches-distr r₁ r₂ (MkCaseBranch body ∷ bs) rewrite act-ε-distr (ext r₁) (ext r₂) body
                                                          | act-branches-distr r₁ r₂ bs
                                                          | act-ε-extensionality (ext-distr r₁ r₂) body = refl


  weaken-τ-comm : ∀ (ρ : Fin ℓ → Fin ℓ') (τ : SType ℓ)
                → act-τ (ext ρ) (weaken-τ τ) ≡ weaken-τ (act-τ ρ τ)
  weaken-τ-comm ρ τ rewrite act-τ-distr suc (ext ρ) τ
                          | act-τ-distr ρ suc τ = refl

  weaken-ε-comm : ∀ (ρ : Fin ℓ → Fin ℓ') (ε : STerm ℓ)
                → act-ε (ext ρ) (weaken-ε ε) ≡ weaken-ε (act-ε ρ ε)
  weaken-ε-comm ρ ε rewrite act-ε-distr suc (ext ρ) ε
                          | act-ε-distr ρ suc ε = refl


module S where
  open ActionScoped (record { Target = STerm
                            ; var-action = λ σ idx → σ idx
                            ; ext = λ where _ zero → SVar zero
                                            σ (suc n) → R.weaken-ε (σ n)
                            }
                    ) public

  ≡-ext : {f₁ f₂ : Fin ℓ → STerm ℓ'}
        → (∀ x → f₁ x ≡ f₂ x)
        → (∀ x → ext f₁ x ≡ ext f₂ x)
  ≡-ext x-≡ zero = refl
  ≡-ext x-≡ (suc x) rewrite x-≡ x = refl

  var-action-cong : {f₁ f₂ : Fin ℓ → STerm ℓ'}
                  → (∀ x → f₁ x ≡ f₂ x)
                  → (∀ x → var-action f₁ x ≡ var-action f₂ x)
  var-action-cong x-≡ x = x-≡ x

  open ActionScopedLemmas var-action-record
                          record { ≡-ext = ≡-ext
                                 ; var-action-cong = var-action-cong
                                 }
                          public


  replace-at : Fin (suc ℓ) → STerm ℓ → Fin (suc ℓ) → STerm ℓ
  replace-at replace-idx ε var-idx with replace-idx <>? var-idx
  -- replacement index is less than current variable index, so the variable points to a binder that just got closer to it,
  -- so decrement the variable index:
  ... | less rep<var = SVar (m<n-n-pred rep<var)
  -- just replace the current variable with the term:
  ... | equal = ε
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


  ext-replace-comm : ∀ ε (ι : Fin (suc ℓ))
                   → (∀ var-idx → ext (replace-at ι ε) var-idx ≡ replace-at (suc ι) (R.act-ε suc ε) var-idx)
  ext-replace-comm _ zero zero = refl
  ext-replace-comm _ (suc ι) zero = refl
  ext-replace-comm _ zero (suc var-idx) with zero <>? var-idx
  ... | less m<n rewrite m<n-n-pred-cancel m<n = refl
  ... | equal = refl
  ext-replace-comm _ (suc ι) (suc var-idx) with suc ι <>? var-idx
  ... | less m<n rewrite m<n-n-pred-cancel m<n = refl
  ... | equal = refl
  ... | greater m>n = refl

  R-ext-replace-comm : ∀ ε (ρ : Fin ℓ → Fin ℓ') ι
                     → (∀ var-idx → ext (replace-at (R.ext ρ ι) (R.act-ε ρ ε)) var-idx ≡ replace-at (suc (R.ext ρ ι)) (R.act-ε (R.ext ρ) (R.act-ε suc ε)) var-idx)
  R-ext-replace-comm ε ρ zero zero = refl
  R-ext-replace-comm ε ρ (suc ι) zero = refl
  R-ext-replace-comm ε ρ zero (suc var-idx) with zero <>? var-idx
  ... | less m<n rewrite m<n-n-pred-cancel m<n = refl
  ... | equal rewrite R.weaken-ε-comm ρ ε = refl
  R-ext-replace-comm ε ρ (suc ι) (suc var-idx) with suc (ρ ι) <>? var-idx
  ... | less m<n rewrite m<n-n-pred-cancel m<n = refl
  ... | equal rewrite R.weaken-ε-comm ρ ε = refl
  ... | greater m>n = refl

  data CommutingRenamer : (ρ : Fin ℓ → Fin ℓ') → (ι : Fin (suc ℓ)) → Set where
    comm-at-zero : ∀ {ρ : Fin ℓ → Fin ℓ'}
                 → (ρ-mono : Monotonic ρ)
                 → CommutingRenamer ρ zero
    comm-at-suc  : ∀ {ρ : Fin (suc ℓ) → Fin (suc ℓ')}
                 → (ρ-mono : Monotonic ρ)
                 → (ρ-zero : ρ zero ≡ zero)
                 → CommutingRenamer ρ (suc ι)

  ext-monotonic : ∀ {ρ : Fin ℓ → Fin ℓ'}
                → Monotonic ρ
                → Monotonic (R.ext ρ)
  ext-monotonic ρ-mono {x = zero} {y = zero} ()
  ext-monotonic ρ-mono {x = zero} {y = suc y} (<-zero .y) = <-zero _
  ext-monotonic ρ-mono {x = suc x} {y = zero} ()
  ext-monotonic ρ-mono {x = suc x} {y = suc y} (<-suc x<y) = <-suc (ρ-mono x<y)

  ext-commuting : ∀ {ρ : Fin ℓ → Fin ℓ'} {ι}
                → CommutingRenamer ρ ι
                → CommutingRenamer (R.ext ρ) (suc ι)
  ext-commuting (comm-at-zero ρ-mono) = comm-at-suc (ext-monotonic ρ-mono) refl
  ext-commuting (comm-at-suc ρ-mono ρ-zero) = comm-at-suc (ext-monotonic ρ-mono) refl

  RenameSubstDistributivity : {Ty : ℕ → Set} → R.ActionOn Ty → SubstOn Ty → Set
  RenameSubstDistributivity {Ty} ρ-act [↦] = ∀ {ℓ ℓ'}
                                             → (ρ : Fin ℓ → Fin ℓ')
                                             → (ε : STerm ℓ)
                                             → (ι : Fin (suc ℓ))
                                             → (ρ-comm : CommutingRenamer ρ ι)
                                             → (v : Ty (suc ℓ))
                                             → ρ-act ρ ([↦] ι ε v) ≡ [↦] (R.ext ρ ι) (R.act-ε ρ ε) (ρ-act (R.ext ρ) v)

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

  rename-subst-var-distr-lemma₁ : ∀ ε (ρ[ι] ρ[idx] : Fin ℓ') (_ : ρ[ι] < ρ[idx])
                                → replace-at (suc (ρ[ι])) ε (suc (ρ[idx])) ≡ SVar (ρ[idx])
  rename-subst-var-distr-lemma₁ _ ρ[ι] ρ[idx] ρ[ι]<ρ[idx] with ρ[ι] <>? ρ[idx]
  ... | less m<n = refl
  ... | equal = ⊥-elim (m<n-not-equal ρ[ι]<ρ[idx] refl)
  ... | greater m>n = ⊥-elim (m<n-not-m>n m>n ρ[ι]<ρ[idx])

  rename-subst-var-distr-lemma₂ : ∀ (ρ : Fin (suc ℓ) → Fin (suc ℓ')) ι
                                → ρ zero ≡ zero
                                → ρ (tighten (<-zero ι)) ≡ tighten (<-zero (ρ ι))
  rename-subst-var-distr-lemma₂ ρ ι ρ-zero rewrite tighten-zero ι
                                                 | tighten-zero (ρ ι) = ρ-zero

  rename-subst-var-distr : ∀ (ρ : Fin ℓ → Fin ℓ') ε (ι : Fin (suc ℓ)) (ρ-comm : CommutingRenamer ρ ι) idx
                         → R.act-ε ρ ([ ι ↦ε ε ] SVar idx) ≡ [ R.ext ρ ι ↦ε R.act-ε ρ ε ] R.act-ε (R.ext ρ) (SVar idx)
  rename-subst-var-distr ρ ε zero _ zero = refl
  rename-subst-var-distr ρ ε zero _ (suc idx) = refl
  rename-subst-var-distr ρ ε (suc ι) (comm-at-suc ρ-mono ρ-zero) zero rewrite rename-subst-var-distr-lemma₂ ρ ι ρ-zero = refl
  rename-subst-var-distr ρ ε (suc ι) (comm-at-suc ρ-mono ρ-zero) (suc idx) with ι <>? idx
  ... | less m<n rewrite rename-subst-var-distr-lemma₁ (R.act-ε ρ ε) (ρ ι) (ρ idx) (ρ-mono m<n) = refl
  ... | equal rewrite <>?-refl-equal (ρ ι) = refl
  ... | greater m>n = {! !}

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

infix 4 _∈_at_
data _∈_at_ : SType ℓ → Ctx ℓ → Fin ℓ → Set where
  ∈-zero : R.weaken-τ τ ∈ (Γ , τ) at zero
  ∈-suc  : τ ∈ Γ at idx
         → R.weaken-τ τ ∈ (Γ , τ') at suc idx

infix 4 _⊂_
record _⊂_ {ℓ ℓ'} (Γ : Ctx ℓ) (Γ' : Ctx ℓ') : Set where
  constructor MkTR
  field
    ρ   : Fin ℓ → Fin ℓ'
    ρ-∈ : τ ∈ Γ at idx
        → R.act-τ ρ τ ∈ Γ' at ρ idx

append-both : ∀ {Γ : Ctx ℓ} {Γ' : Ctx ℓ'} {τ₀ : SType ℓ}
            → (Γ⊂Γ' : Γ ⊂ Γ')
            → Γ , τ₀ ⊂ Γ' , R.act-τ (_⊂_.ρ Γ⊂Γ') τ₀
append-both {Γ = Γ} {Γ' = Γ'} (MkTR ρ ρ-∈) = MkTR (R.ext ρ) ρ-∈'
  where
    ρ-∈' : τ ∈ Γ , τ' at idx
         → R.act-τ (R.ext ρ) τ ∈ Γ' , R.act-τ ρ τ' at R.ext ρ idx
    ρ-∈' {τ' = τ'} ∈-zero rewrite R.weaken-τ-comm ρ τ' = ∈-zero
    ρ-∈' (∈-suc {τ = τ} x) rewrite R.weaken-τ-comm ρ τ = ∈-suc (ρ-∈ x)
