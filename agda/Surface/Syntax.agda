module Surface.Syntax where

open import Agda.Builtin.Bool
open import Agda.Builtin.List public
open import Agda.Builtin.Nat public
open import Agda.Builtin.String

open import Data.Bool using (if_then_else_)
open import Data.Fin public using (Fin)
open import Data.Product public using (_×_)
open import Data.Vec public

-- Syntax definitions

record Var : Set where
  constructor MkVar
  field
    var : String

open Var

var-eq : Var → Var → Bool
var-eq x₁ x₂ = primStringEquality (var x₁) (var x₂)

data BaseType : Set where
  BUnit : BaseType


data STerm : Set
data SType : Set
data Refinement : Set
CaseBranches : Nat → Set
ADTCons : Nat → Set

record CaseBranch : Set

data STerm where
  SVar  : (var : Var) → STerm
  SLam  : (var : Var) → (τ : SType) → (ε : STerm) → STerm
  SApp  : (ε₁ : STerm) → (ε₂ : STerm) → STerm
  SUnit : STerm
  SCase : {n : _} → (scrut : STerm) → (branches : CaseBranches n) → STerm
  SCon  : {n : _} → (idx : Fin n) → (body : STerm) → (adtCons : ADTCons n) → STerm

data SType where
  SRBT : (var : Var) → (b : BaseType) → (ρ : Refinement) → SType
  SArr : (var : Var) → (τ₁ : SType) → (τ₂ : SType) → SType
  SADT : {n : _} → (cons : ADTCons (suc n)) → SType

data Refinement where
  _≈_ : STerm → STerm → Refinement
  _∧_ : (ρ₁ : Refinement) → (ρ₂ : Refinement) → Refinement

record CaseBranch where
  constructor MkCaseBranch
  inductive
  field
    var : Var
    body : STerm

CaseBranches n = Vec CaseBranch n

ADTCons n = Vec SType n


CtxElem : Set
CtxElem = Var × SType

Ctx : Set
Ctx = List CtxElem


-- Substitutions

SubstIn : Set → Set
SubstIn ty = Var → STerm → ty → ty

substInType : SubstIn SType
substInRef : SubstIn Refinement
substInTerm : SubstIn STerm
substInADT : {n : _} → SubstIn (ADTCons n)
substInBranches : {n : _} → SubstIn (CaseBranches n)

substInType x ε (SRBT var b ρ) = SRBT var b (substInRef x ε ρ)
substInType x ε (SArr var τ₁ τ₂) = SArr var (substInType x ε τ₁) (substInType x ε τ₂)
substInType x ε (SADT cons) = SADT (substInADT x ε cons)

substInRef x ε (ε₁ ≈ ε₂) = substInTerm x ε ε₁ ≈ substInTerm x ε ε₂
substInRef x ε (ρ₁ ∧ ρ₂) = substInRef x ε ρ₁ ∧ substInRef x ε ρ₂

substInTerm x ε (SVar var) = if var-eq x var
                             then ε
                             else SVar var
substInTerm x ε (SLam var τ ε') = if var-eq x var
                                  then SLam var τ ε'
                                  else ε
substInTerm x ε (SApp ε₁ ε₂) = SApp (substInTerm x ε ε₁) (substInTerm x ε ε₂)
substInTerm x ε SUnit = SUnit
substInTerm x ε (SCase scrut branches) = SCase (substInTerm x ε scrut) (substInBranches x ε branches)
substInTerm x ε (SCon idx body adtCons) = SCon idx (substInTerm x ε body) (substInADT x ε adtCons)

substInADT x ε [] = []
substInADT x ε (τ ∷ τs) = substInType x ε τ ∷ substInADT x ε τs

substInBranches x ε [] = []
substInBranches x ε (MkCaseBranch v body ∷ bs) =
  let body' = if var-eq x v
              then body
              else substInTerm x ε body
      rest = substInBranches x ε bs
   in MkCaseBranch v body' ∷ rest

[_↦_]_ : SubstIn SType
[ x ↦ ε ] τ = substInType x ε τ
