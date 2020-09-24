module Surface.Substitutions where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Data.Bool using (if_then_else_)
open import Data.List.Base hiding (lookup)
open import Data.Vec using ([] ; _∷_ ; lookup)

open import Surface.Syntax

SubstIn : Set → Set
SubstIn ty = Var → STerm → ty → ty

infix 30 [_↦ₜ_]_ [_↦ₑ_]_ [_↦ᵣ_]_ [_↦ₗ_]_ [_↦ₐ_]_ [_↦ₘ_]_
[_↦ₜ_]_ : SubstIn SType
[_↦ₑ_]_ : SubstIn STerm
[_↦ᵣ_]_ : SubstIn Refinement

[_↦ₐ_]_ : {n : _} → SubstIn (ADTCons n)
substInBranches : {n : _} → SubstIn (CaseBranches n)

[ x ↦ₜ ε ] (SRBT var b ρ) = SRBT var b ([ x ↦ᵣ ε ] ρ)
[ x ↦ₜ ε ] (SArr var τ₁ τ₂) = SArr var ([ x ↦ₜ ε ] τ₁) ([ x ↦ₜ ε ] τ₂)
[ x ↦ₜ ε ] (SADT cons) = SADT ([ x ↦ₐ ε ] cons)

[ x ↦ᵣ ε ] (ε₁ ≈ ε₂) = [ x ↦ₑ ε ] ε₁ ≈ [ x ↦ₑ ε ] ε₂
[ x ↦ᵣ ε ] (ρ₁ ∧ ρ₂) = [ x ↦ᵣ ε ] ρ₁ ∧ [ x ↦ᵣ ε ] ρ₂

[ x ↦ₑ ε ] (SVar var) = if var-eq x var
                             then ε
                             else SVar var
[ x ↦ₑ ε ] (SLam var τ ε') = if var-eq x var
                                  then SLam var τ ε'
                                  else ε
[ x ↦ₑ ε ] (SApp ε₁ ε₂) = SApp ([ x ↦ₑ ε ] ε₁) ([ x ↦ₑ ε ] ε₂)
[ x ↦ₑ ε ] SUnit = SUnit
[ x ↦ₑ ε ] (SCase scrut branches) = SCase ([ x ↦ₑ ε ] scrut) (substInBranches x ε branches)
[ x ↦ₑ ε ] (SCon idx body adtCons) = SCon idx ([ x ↦ₑ ε ] body) ([ x ↦ₐ ε ] adtCons)

[ x ↦ₐ ε ] [] = []
[ x ↦ₐ ε ] (τ ∷ τs) = [ x ↦ₜ ε ] τ ∷ [ x ↦ₐ ε ] τs

substInBranches x ε [] = []
substInBranches x ε (MkCaseBranch v body ∷ bs) =
  let body' = if var-eq x v
              then body
              else [ x ↦ₑ ε ] body
      rest = substInBranches x ε bs
   in MkCaseBranch v body' ∷ rest

[_↦ₗ_]_ : SubstIn Ctx
[ x ↦ₗ ε ] [] = []
[ x ↦ₗ ε ] ((x' , τ) ∷ ctx) = (x' , [ x ↦ₜ ε ] τ) ∷ [ x ↦ₗ ε ] ctx

[_↦ₘ_]_ : Fin n → STerm → CaseBranches n → STerm
[ idx ↦ₘ ε ] branches = [ var ↦ₑ ε ] body
  where open CaseBranch (lookup branches idx)

sub-ctx-snoc : ∀ x ε y τ Δ → [ x ↦ₗ ε ] (Δ ++ [ (y , τ) ]) ≡ [ x ↦ₗ ε ] Δ ++ [ (y , [ x ↦ₜ ε ] τ) ]
sub-ctx-snoc _ _ _ _ [] = refl
sub-ctx-snoc x ε y τ ( _  ∷ Δ) rewrite sub-ctx-snoc x ε y τ Δ = refl
