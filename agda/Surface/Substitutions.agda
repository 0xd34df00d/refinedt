module Surface.Substitutions where

open import Data.Bool using (if_then_else_)

open import Surface.Syntax

SubstIn : Set → Set
SubstIn ty = Var → STerm → ty → ty

infix 30 [_↦ₜ_]_ [_↦ₑ_]_ [_↦ᵣ_]_
[_↦ₜ_]_ : SubstIn SType
[_↦ₑ_]_ : SubstIn STerm
[_↦ᵣ_]_ : SubstIn Refinement

substInADT : {n : _} → SubstIn (ADTCons n)
substInBranches : {n : _} → SubstIn (CaseBranches n)

[ x ↦ₜ ε ] (SRBT var b ρ) = SRBT var b ([ x ↦ᵣ ε ] ρ)
[ x ↦ₜ ε ] (SArr var τ₁ τ₂) = SArr var ([ x ↦ₜ ε ] τ₁) ([ x ↦ₜ ε ] τ₂)
[ x ↦ₜ ε ] (SADT cons) = SADT (substInADT x ε cons)

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
[ x ↦ₑ ε ] (SCon idx body adtCons) = SCon idx ([ x ↦ₑ ε ] body) (substInADT x ε adtCons)

substInADT x ε [] = []
substInADT x ε (τ ∷ τs) = [ x ↦ₜ ε ] τ ∷ substInADT x ε τs

substInBranches x ε [] = []
substInBranches x ε (MkCaseBranch v body ∷ bs) =
  let body' = if var-eq x v
              then body
              else [ x ↦ₑ ε ] body
      rest = substInBranches x ε bs
   in MkCaseBranch v body' ∷ rest
