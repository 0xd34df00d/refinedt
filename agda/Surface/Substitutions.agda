module Surface.Substitutions where

open import Data.Bool using (if_then_else_)

open import Surface.Syntax

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
