{-# OPTIONS --safe #-}

module Intermediate.Syntax where

open import Data.Fin public using (Fin)
open import Data.Nat public using (ℕ; suc)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Common.Types public

data BaseType : Set where
  BUnit : BaseType

variable
  b b' b₁ b₂ : BaseType

data IType (ℓ : ℕ) : Set
data ITerm (ℓ : ℕ) : Set
data IRefinement (ℓ : ℕ) : Set

ADTCons : ℕₐ → ℕ → Set
ADTCons (Mkℕₐ n) ℓ = Vec (IType ℓ) n

record CaseBranch (ℓ : ℕ) : Set where
  constructor MkCaseBranch
  inductive
  field
    body : ITerm (suc ℓ)

CaseBranches : ℕₐ → ℕ → Set
CaseBranches (Mkℕₐ n) ℓ = Vec (CaseBranch ℓ) n

data IType ℓ where
  ⟨_∣_⟩ : (b : BaseType)
        → (ρ : IRefinement (suc ℓ))
        → IType ℓ
  _⇒_   : (τ₁ : IType ℓ)
        → (τ₂ : IType (suc ℓ))
        → IType ℓ
  ⊍_    : (cons : ADTCons (Mkℕₐ n) ℓ)
        → IType ℓ

data ITerm ℓ where
  IUnit : ITerm ℓ
  IVar  : (ι : Fin ℓ)
        → ITerm ℓ
  ILam  : (τ : IType ℓ)
        → (ε : ITerm (suc ℓ))
        → ITerm ℓ
  IApp  : (ε₁ ε₂ : ITerm ℓ)
        → ITerm ℓ
  ICase : (scrut : ITerm ℓ)
        → (branches : CaseBranches nₐ ℓ)
        → ITerm ℓ
  ICon  : (ι : Fin n)
        → (body : ITerm ℓ)
        → (adt-cons : ADTCons (Mkℕₐ n) ℓ)
        → ITerm ℓ
  _I<:_ : (ε : ITerm ℓ)
        → (τ : IType ℓ)
        → ITerm ℓ
-- NOTE: ε I<: τ is a syntactic witness that subtyping was used to assign type τ to a term ε,
-- where Γ ⊢ ε : τ' and τ' <: τ.
-- I'm not sure whether the original type τ' shall be carried around on the syntax level:
-- uniqueness of types, which shall hold for this type system, guarantees that at most one type
-- can be assigned to ε, so I think there's no need to, but I might be wrong.

data IRefinement ℓ where
  _≈_of_ : (ε₁ ε₂ : ITerm ℓ) → (τ : IType ℓ) → IRefinement ℓ
  _∧_    : (ρ₁ ρ₂ : IRefinement ℓ) → IRefinement ℓ
  Τ      : IRefinement ℓ


infixl 5 _,_
data Ctx : ℕ → Set where
  ⊘   : Ctx 0
  _,_ : Ctx ℓ → IType ℓ → Ctx (suc ℓ)

variable
  Γ Γ' : Ctx ℓ
  τ τ' τ₀ τ₀' τ₁ τ₂ τ₁' τ₂' τ₃ τ₃' τᵢ τⱼ σ σ' : IType ℓ
  ε ε' ε₀ ε₁ ε₁' ε₂ ε₂' ε₃ ε₃' ϖ : ITerm ℓ
  ρ ρ₁ ρ₂ ρ₃ : IRefinement ℓ

record VarAction : Set₁ where
  field
    Target : ℕ → Set
    var-action : Target ℓ → ITerm ℓ
    ext : (Fin ℓ → Target ℓ')
        → (Fin (suc ℓ) → Target (suc ℓ'))

record VarActionProps (act : VarAction) : Set where
  open VarAction act
  field
    ≡-ext : {f₁ f₂ : Fin ℓ → Target ℓ'}
          → (∀ x → f₁ x ≡ f₂ x)
          → (∀ x → ext f₁ x ≡ ext f₂ x)
    ext-id : ∀ {f : Fin ℓ → Target ℓ}
           → (∀ x → var-action (f x) ≡ IVar x)
           → (∀ x → var-action (ext f x) ≡ IVar x)
