{-# OPTIONS --safe #-}

module Surface.WellScoped where

open import Agda.Builtin.Bool
open import Agda.Builtin.List public
open import Agda.Builtin.String

open import Data.Nat.Base public
open import Data.Fin public using (Fin; suc; zero)
open import Data.Vec

data BaseType : Set where
  BUnit : BaseType

record ℕₐ : Set where
  constructor Mkℕₐ
  field
    get-length : ℕ

variable
  n ℓ ℓ' : ℕ
  nₐ : ℕₐ
  b b' b₁ b₂ : BaseType
  idx : Fin ℓ

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
  τ τ' τ₁ τ₂ τ₁' τ₂' : SType ℓ
  ε ε' ε₁ ε₂ : STerm ℓ
  ρ₁ ρ₂ : Refinement ℓ

Τ : Refinement ℓ
Τ = SUnit ≈ SUnit

record VarsAction : Set₁ where
  field
    Target : ℕ → Set
    var-action : (Fin ℓ → Target ℓ')
               → (Fin ℓ → STerm ℓ')
    ext : (Fin ℓ → Target ℓ')
        → (Fin (suc ℓ) → Target (suc ℓ'))

module ActionScoped (act : VarsAction) where
  open VarsAction act

  ActionOn : (ℕ → Set) → Set
  ActionOn Ty = ∀ {ℓ ℓ'} → (Fin ℓ → Target ℓ') → Ty ℓ → Ty ℓ'

  act-ρ : ActionOn Refinement
  act-τ : ActionOn SType
  act-ε : ActionOn STerm
  act-cons : ActionOn (ADTCons nₐ)

  act-ρ f (ε₁ ≈ ε₂) = act-ε f ε₁ ≈ act-ε f ε₂
  act-ρ f (ρ₁ ∧ ρ₂) = act-ρ f ρ₁ ∧ act-ρ f ρ₂

  act-τ f ⟨ b ∣ ρ ⟩ = ⟨ b ∣ act-ρ (ext f) ρ ⟩
  act-τ f (τ₁ ⇒ τ₂) = act-τ f τ₁ ⇒ act-τ (ext f) τ₂
  act-τ f (⊍ cons)  = ⊍ (act-cons f cons)

  act-cons _ [] = []
  act-cons f (τ ∷ τs) = act-τ f τ ∷ act-cons f τs

  act-ε f SUnit = SUnit
  act-ε f (SVar idx) = var-action f idx
  act-ε f (SLam τ ε) = SLam (act-τ f τ) (act-ε (ext f) ε)
  act-ε f (SApp ε₁ ε₂) = SApp (act-ε f ε₁) (act-ε f ε₂)
  act-ε f (SCase scrut branches) = SCase (act-ε f scrut) (go f branches)
    where
      go : ∀ {n} → (Fin ℓ → Target ℓ') → CaseBranches n ℓ → CaseBranches n ℓ'
      go _ [] = []
      go f (MkCaseBranch body ∷ bs) = MkCaseBranch (act-ε (ext f) body) ∷ go f bs
  act-ε f (SCon idx body adt-cons) = SCon idx (act-ε f body) (act-cons f adt-cons)

module RenameScoped where
  open ActionScoped (record { Target = Fin
                            ; var-action = λ r idx → SVar (r idx)
                            ; ext = λ where _ zero → zero
                                            r (suc n) → suc (r n)
                            })

  weaken-τ : SType ℓ → SType (suc ℓ)
  weaken-τ = act-τ suc

  weaken-ε : STerm ℓ → STerm (suc ℓ)
  weaken-ε = act-ε suc

module SubstScoped where
  open ActionScoped (record { Target = STerm
                            ; var-action = λ σ idx → σ idx
                            ; ext = λ where _ zero → SVar zero
                                            σ (suc n) → RenameScoped.weaken-ε (σ n)
                            })

infix 4 _∈_at_
data _∈_at_ : SType ℓ → Ctx ℓ → Fin ℓ → Set where
  ∈-zero : RenameScoped.weaken-τ τ ∈ (Γ , τ) at zero
  ∈-suc  : τ ∈ Γ at idx
         → RenameScoped.weaken-τ τ ∈ (Γ , τ') at suc idx
