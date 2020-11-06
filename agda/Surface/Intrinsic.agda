-- {-# OPTIONS --safe #-}

module Surface.Intrinsic where

data BaseType : Set where
  BUnit : BaseType

data Context : Set
data SType : Context → Set
data STerm : (Γ : Context) → SType Γ → Set
data Refinement : BaseType → Context → Set

variable
  b : BaseType
  Γ Γ' Δ : Context

infix 5 _,_
data Context where
  ⊘   : Context
  _,_ : (Γ : Context) → SType Γ → Context

infix 4 _is-prefix_
data _is-prefix_ : Context → Context → Set where
  is-prefix-refl : Γ is-prefix Γ
  is-prefix-snoc : ∀ {τ : SType Γ} → Γ' is-prefix Γ → Γ' is-prefix Γ , τ

data SType where
  ⟨_∣_⟩ : (b : BaseType) → (ρ : Refinement b Γ) → SType Γ
  _⇒_   : (τ : SType Γ) → SType (Γ , τ) → SType Γ
  -- TODO adt

_,`_ : Context → BaseType → Context
_,`_ Γ b = Γ , ⟨ b ∣ {! !} ⟩

data Refinement where
  _≈_ : ∀ {τ : SType (Γ ,` b)} → STerm (Γ ,` b) τ → STerm (Γ ,` b) τ → Refinement b Γ
  _∧_ : ∀ (ρ₁ ρ₂ : Refinement b Γ) → Refinement b Γ
  ⊤R  : Refinement b Γ

infix 4 _∈_
data _∈_ : SType Γ → Context → Set where
  ∈-zero : ∀ {τ : SType Γ'} → τ ∈ Γ' , τ
--  ∈-suc  : ∀ {τ : SType Γ'} → τ ∈ Γ' → τ ∈ Γ' , τ'

data STerm where
  SVar : ∀ {τ : SType Γ} → τ ∈ Γ → STerm Γ τ
