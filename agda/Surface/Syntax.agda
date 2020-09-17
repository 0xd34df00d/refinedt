module Surface.Syntax where

open import Agda.Builtin.Bool
open import Agda.Builtin.List public
open import Agda.Builtin.String

open import Data.Nat.Base public
open import Data.Fin public using (Fin)
open import Data.Product public using (_×_)
open import Data.Product using (_,_)
open import Data.Vec public hiding (_++_)

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
CaseBranches : ℕ → Set
ADTCons : ℕ → Set

record CaseBranch : Set

data STerm where
  SVar  : (var : Var) → STerm
  SLam  : (var : Var) → (τ : SType) → (ε : STerm) → STerm
  SApp  : (ε₁ : STerm) → (ε₂ : STerm) → STerm
  SUnit : STerm
  SCase : {n : _} → (scrut : STerm) → (branches : CaseBranches n) → STerm
  SCon  : {n : _} → (idx : Fin n) → (body : STerm) → (adtCons : ADTCons n) → STerm

data SType where
  SRBT : (ν : Var) → (b : BaseType) → (ρ : Refinement) → SType
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

infixl 20 _,_⦂_
_,_⦂_ : Ctx → Var → SType → Ctx
Γ , x ⦂ τ = ( x , τ ) ∷ Γ

infix 19 _⦂_
_⦂_ : Var → SType → Var × SType
_⦂_ = _,_

infix 15 _∈_∣_
_∈_∣_ : (ν : Var) → (b : BaseType) → (ρ : Refinement) → SType
_∈_∣_ = SRBT

Τ : Refinement
Τ = SUnit ≈ SUnit

variable
  Γ Γ' Δ : Ctx
  x x' x₁ x₂ ν ν₁ ν₂ : Var
  τ τ' τ₁ τ₂ τ₁' τ₂' τᵢ τⱼ : SType
  ε ε' ε₁ ε₂ : STerm
  b b' : BaseType
  ρ₁ ρ₂ : Refinement
  n : ℕ
