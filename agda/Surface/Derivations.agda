module Surface.Derivations where

open import Agda.Builtin.Unit
open import Data.Maybe
open import Data.List.Membership.Propositional
open import Data.Vec.Relation.Unary.All

open import Surface.Syntax
open import Surface.Substitutions

record PositiveDecision : Set where
  constructor MkPD

record Oracle : Set where
  constructor MkOracle
  field
    decide : (var : Var) → (b : BaseType) → (ρ₁ : Refinement) → (ρ₂ : Refinement) → Maybe PositiveDecision

variable
  Γ : Ctx
  x x' ν ν₁ ν₂ : Var
  τ τ' τ₁ τ₂ : SType
  ε ε₁ ε₂ : STerm
  b b' : BaseType
  ρ₁ ρ₂ : Refinement

data _ok : (Γ : Ctx) → Set
data _⊢_⦂_ : (Γ : Ctx) → (ε : STerm) → (τ : SType) → Set
data _⊢'_ : (Γ : Ctx) → (τ : SType) → Set

data _ok where
  TCTX_Empty : [] ok
  TCTX_Bind  : (prevOk : Γ ok)
             → (τδ : Γ ⊢' τ)
             → (Γ ,, ν ∷ τ) ok

data _⊢'_ where
  TWF_TrueRef : Γ ⊢' (ν ∈ b ∣ Τ)
  TWF_Base    : (ε₁δ : (Γ ,, ν ∷ (ν₁ ∈ b ∣ Τ)) ⊢ ε₁ ⦂ (ν₂ ∈ b' ∣ Τ))
              → (ε₂δ : (Γ ,, ν ∷ (ν₁ ∈ b ∣ Τ)) ⊢ ε₂ ⦂ (ν₂ ∈ b' ∣ Τ))
              → Γ ⊢' (ν ∈ b ∣ ε₁ ≈ ε₂)
  TWF_Conj    : (ρ₁δ : Γ ⊢' (ν ∈ b ∣ ρ₁))
              → (ρ₂δ : Γ ⊢' (ν ∈ b ∣ ρ₂))
              → Γ ⊢' (ν ∈ b ∣ ρ₁ ∧ ρ₂)
  TWF_Arr     : (argδ : Γ ⊢' τ₁)
              → (resδ : (Γ ,, x ∷ τ₁) ⊢' τ₂)
              → Γ ⊢' SArr x τ₁ τ₂
  TWF_ADT     : ∀ {adtCons}
              → (consδs : All (λ conTy → Γ ⊢' conTy) adtCons)
              → Γ ⊢' SADT adtCons

data _⊢_⦂_ where
  T_Unit      : (gok : Γ ok)
              → Γ ⊢ SUnit ⦂ (ν ∈ BUnit ∣ Τ)
  T_Var       : (gok : Γ ok)
              → (x , τ) ∈ Γ
              → Γ ⊢ SVar x ⦂ τ
  T_Abs       : (arrδ : Γ ⊢' SArr x τ₁ τ₂)
              → (bodyδ : (Γ ,, x ∷ τ₁) ⊢ ε ⦂ τ₂)
              → (Γ ⊢ SLam x τ₁ ε ⦂ SArr x τ₁ τ₂)
  T_App       : (δ₁ : Γ ⊢ ε₁ ⦂ SArr x τ₁ τ₂)
              → (δ₂ : Γ ⊢ ε₂ ⦂ τ₁)
              → Γ ⊢ SApp ε₁ ε₂ ⦂ [ x ↦ ε₂ ] τ₂
