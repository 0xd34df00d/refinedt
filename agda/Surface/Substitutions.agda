{-# OPTIONS --safe #-}

module Surface.Substitutions where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Data.Bool using (if_then_else_)
open import Data.Fin
open import Data.List.Base hiding (lookup)
open import Data.Vec using ([] ; _∷_ ; lookup)

open import Surface.Syntax
open import Common.NamingContext

-- Define shifts first
-- A good source on this is, of course, Pierce's TAPL, chapter 6.

open NamingCtx

record Cutoff (Γ↓ : NamingCtx) : Set where
  constructor MkCutoff
  field
    cutoff : Fin (suc (ctx-len Γ↓))

open Cutoff

zero-cutoff : Cutoff Γ↓
zero-cutoff = MkCutoff zero

inc-cutoff : Cutoff Γ↓ → Cutoff (expand-Γ↓ Γ↓)
inc-cutoff (MkCutoff c) = MkCutoff (suc c)

ShiftType : (NamingCtx → Set) → Set
ShiftType ty = ∀ {Γ↓} → Cutoff Γ↓ → ty Γ↓ → ty (expand-Γ↓ Γ↓)

shift-ε'    : ShiftType STerm
shift-τ'    : ShiftType SType
shift-ρ'    : ShiftType Refinement
shift-b'    : ShiftType CaseBranch
shift-bs'   : ShiftType (CaseBranches n)
shift-cons' : ShiftType (ADTCons n)

shift-ε' c (SVar var) with raise 1 var
... | var↑ with compare var↑ (cutoff c)
... | less _ _ = SVar var↑
... | _ = SVar (suc var)
shift-ε' c (SLam τ ε) = SLam (shift-τ' c τ) (shift-ε' (inc-cutoff c) ε)
shift-ε' c (SApp ε₁ ε₂) = SApp (shift-ε' c ε₁) (shift-ε' c ε₂)
shift-ε' c SUnit = SUnit
shift-ε' c (SCase ε branches) = SCase (shift-ε' c ε) (shift-bs' c branches)
shift-ε' c (SCon idx ε adtCons) = SCon idx (shift-ε' c ε) (shift-cons' c adtCons)

shift-b' c (MkCaseBranch body) = MkCaseBranch (shift-ε' (inc-cutoff c) body)

shift-bs' c [] = []
shift-bs' c (b ∷ bs) = shift-b' c b ∷ shift-bs' c bs

shift-cons' c [] = []
shift-cons' c (τ ∷ cons) = shift-τ' c τ ∷ shift-cons' c cons

shift-τ' c (SRBT b ρ) = SRBT b (shift-ρ' (inc-cutoff c) ρ)
shift-τ' c (SArr τ₁ τ₂) = SArr (shift-τ' c τ₁) (shift-τ' (inc-cutoff c) τ₂)
shift-τ' c (SADT cons) = SADT (shift-cons' c cons)

shift-ρ' c (ε₁ ≈ ε₂) = shift-ε' c ε₁ ≈ shift-ε' c ε₂
shift-ρ' c (ρ₁ ∧ ρ₂) = shift-ρ' c ρ₁ ∧ shift-ρ' c ρ₂

shift-ε : STerm Γ↓ → STerm (expand-Γ↓ Γ↓)
shift-ε = shift-ε' zero-cutoff

shift-τ : SType Γ↓ → SType (expand-Γ↓ Γ↓)
shift-τ = shift-τ' zero-cutoff

shift-ρ : Refinement Γ↓ → Refinement (expand-Γ↓ Γ↓)
shift-ρ = shift-ρ' zero-cutoff


SubstIn : (NamingCtx → Set) → Set
SubstIn ty = ∀ {Γ↓} → Var Γ↓ → STerm Γ↓ → ty Γ↓ → ty Γ↓

infix 30 [_↦ₜ_]_ [_↦ₑ_]_ [_↦ᵣ_]_ [_↦ₗ_]_ [_↦ₐ_]_ [_↦ₘ_]_
[_↦ₜ_]_ : SubstIn SType
[_↦ₑ_]_ : SubstIn STerm
[_↦ᵣ_]_ : SubstIn Refinement

[_↦ₐ_]_ : {n : _} → SubstIn (ADTCons n)
substInBranches : {n : _} → SubstIn (CaseBranches n)

[ x ↦ₜ ε ] (SRBT b ρ) = SRBT b ([ suc x ↦ᵣ shift-ε ε ] ρ)
[ x ↦ₜ ε ] (SArr τ₁ τ₂) = SArr ([ x ↦ₜ ε ] τ₁) ([ suc x ↦ₜ shift-ε ε ] τ₂)
[ x ↦ₜ ε ] (SADT cons) = SADT ([ x ↦ₐ ε ] cons)

[ x ↦ᵣ ε ] (ε₁ ≈ ε₂) = [ x ↦ₑ ε ] ε₁ ≈ [ x ↦ₑ ε ] ε₂
[ x ↦ᵣ ε ] (ρ₁ ∧ ρ₂) = [ x ↦ᵣ ε ] ρ₁ ∧ [ x ↦ᵣ ε ] ρ₂

[ x ↦ₑ ε ] (SVar var) = if var-eq x var
                        then ε
                        else SVar var
[ x ↦ₑ ε ] (SLam τ ε') = SLam ([ x ↦ₜ ε ] τ) ([ suc x ↦ₑ shift-ε ε ] ε')
[ x ↦ₑ ε ] (SApp ε₁ ε₂) = SApp ([ x ↦ₑ ε ] ε₁) ([ x ↦ₑ ε ] ε₂)
[ x ↦ₑ ε ] SUnit = SUnit
[ x ↦ₑ ε ] (SCase scrut branches) = SCase ([ x ↦ₑ ε ] scrut) (substInBranches x ε branches)
[ x ↦ₑ ε ] (SCon idx body adtCons) = SCon idx ([ x ↦ₑ ε ] body) ([ x ↦ₐ ε ] adtCons)

[ x ↦ₐ ε ] [] = []
[ x ↦ₐ ε ] (τ ∷ τs) = [ x ↦ₜ ε ] τ ∷ [ x ↦ₐ ε ] τs

substInBranches x ε [] = []
substInBranches x ε (MkCaseBranch body ∷ bs) = MkCaseBranch ([ suc x ↦ₑ shift-ε ε ] body) ∷ substInBranches x ε bs

{-
[_↦ₗ_]_ : SubstIn Ctx
[ x ↦ₗ ε ] [] = []
[ x ↦ₗ ε ] ((x' , τ) ∷ ctx) = (x' , [ x ↦ₜ ε ] τ) ∷ [ x ↦ₗ ε ] ctx

sub-ctx-snoc : ∀ x ε y τ Δ → [ x ↦ₗ ε ] (Δ ++ [ (y , τ) ]) ≡ [ x ↦ₗ ε ] Δ ++ [ (y , [ x ↦ₜ ε ] τ) ]
sub-ctx-snoc _ _ _ _ [] = refl
sub-ctx-snoc x ε y τ ( _  ∷ Δ) rewrite sub-ctx-snoc x ε y τ Δ = refl
-}

[_↦ₘ_]_ : Fin n → STerm Γ↓ → CaseBranches n Γ↓ → STerm Γ↓
[ idx ↦ₘ ε ] branches = [ {! closest-var !} ↦ₑ {! !} ] body
  where open CaseBranch (lookup branches idx)
