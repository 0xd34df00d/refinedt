{-# OPTIONS --safe #-}

module Core.Syntax where

open import Agda.Builtin.Bool
open import Agda.Builtin.List public
open import Agda.Builtin.String
open import Data.Bool using (if_then_else_ ; _∨_)
open import Data.Fin public using (Fin)
open import Data.Nat.Base public
open import Data.Product public using (_×_)
open import Data.Product using (_,_)
open import Data.Vec.Base

data Sort : Set where
  ⋆ : Sort
  □ : Sort

record Var : Set where
  constructor MkVar
  field
    var : String

open Var

var-eq : Var → Var → Bool
var-eq x₁ x₂ = primStringEquality (var x₁) (var x₂)

ADTCons : ℕ → Set
CaseBranches : ℕ → Set

record CaseBranch : Set

data CExpr : Set where
  CVar  : (var : Var) → CExpr
  CSort : (s : Sort) → CExpr
  CPi   : (var : Var) → (ε₁ ε₂ : CExpr) → CExpr
  CLam  : (var : Var) → (ε₁ ε₂ : CExpr) → CExpr
  CApp  : (ε₁ ε₂ : CExpr) → CExpr
  Cunit : CExpr
  CUnit : CExpr
  CADT  : ∀ {n} → (cons : ADTCons n) → CExpr
  CCon  : ∀ {n} → (idx : Fin n) → (body : CExpr) → (cons : ADTCons n) → CExpr
  CCase : ∀ {n} → (scrut : CExpr) → (branches : CaseBranches n) → CExpr

ADTCons = Vec CExpr
CaseBranches = Vec CaseBranch

record CaseBranch where
  constructor MkCaseBranch
  inductive
  field
    x : Var
    π : Var
    body : CExpr

CtxElem : Set
CtxElem = Var × CExpr

Ctx : Set
Ctx = List CtxElem

infixl 21 _,_⦂_
_,_⦂_ : Ctx → Var → CExpr → Ctx
Γ , x ⦂ τ = ( x , τ ) ∷ Γ

infix 19 _⦂_
_⦂_ : Var → CExpr → Var × CExpr
_⦂_ = _,_

variable
  Γ Γ' Δ : Ctx
  x x' x₁ x₂ y ν ν₁ ν₂ : Var
  τ τ' τ₁ τ₂ τ₁' τ₂' τᵢ τⱼ σ : CExpr
  ε ε' ε₁ ε₂ ε₃ ε₁' ε₂' ϖ : CExpr
  b b' b₁ b₂ : CExpr
  n : ℕ
  s s₁ s₂ : Sort


substCons : Var → CExpr → ADTCons n → ADTCons n

infix 30 [_↦_]_
[_↦_]_ : Var → CExpr → CExpr → CExpr
[ x ↦ ε ] CVar var = if var-eq x var then ε else CVar var
[ x ↦ ε ] CSort s = CSort s
[ x ↦ ε ] CPi var ε₁ ε₂ = let ε₁' = [ x ↦ ε ] ε₁
                              ε₂' = if var-eq x var then ε₂ else [ x ↦ ε ] ε₂
                           in CPi var ε₁' ε₂'
[ x ↦ ε ] CLam var ε₁ ε₂ = let ε₁' = [ x ↦ ε ] ε₁
                               ε₂' = if var-eq x var then ε₂ else [ x ↦ ε ] ε₂
                            in CLam var ε₁' ε₂'
[ x ↦ ε ] CApp ε₁ ε₂ = CApp ([ x ↦ ε ] ε₁) ([ x ↦ ε ] ε₂)
[ x ↦ ε ] Cunit = Cunit
[ x ↦ ε ] CUnit = CUnit
[ x ↦ ε ] CADT cons = CADT (substCons x ε cons)
[ x ↦ ε ] CCon idx ε' cons = CCon idx ([ x ↦ ε ] ε') (substCons x ε cons)
[ x ↦ ε ] CCase ε' branches = CCase ([ x ↦ ε ] ε') (go branches)
  where
    go : CaseBranches n → CaseBranches n
    go [] = []
    go (b@(MkCaseBranch x' π body) ∷ bs) = let b = if var-eq x x' ∨ var-eq x π
                                                    then b
                                                    else MkCaseBranch x' π ([ x ↦ ε ] body)
                                            in b ∷ go bs

substCons x ε [] = []
substCons x ε (con ∷ cons) = [ x ↦ ε ] con ∷ substCons x ε cons
