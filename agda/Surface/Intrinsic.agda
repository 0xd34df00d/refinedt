-- {-# OPTIONS --safe #-}

module Surface.Intrinsic where

data BaseType : Set where
  BUnit : BaseType

data Context : Set
data SType (Γ : Context) : Set
data Refinement (b : BaseType) (Γ : Context) : Set
data STerm (Γ : Context) : SType Γ → Set

variable
  b : BaseType
  Γ Γ' Δ : Context

infixl 5 _,_
data Context where
  ⊘   : Context
  _,_ : (Γ : Context) → SType Γ → Context

infix 4 _is-prefix-of_
data _is-prefix-of_ : Context → Context → Set where
  is-prefix-of-refl : Γ is-prefix-of Γ
  is-prefix-of-snoc : ∀ {τ : SType Γ} → Γ' is-prefix-of Γ → Γ' is-prefix-of Γ , τ

data SType Γ where
  ⟨_∣_⟩ : (b : BaseType) → (ρ : Refinement b Γ) → SType Γ
  _⇒_   : (τ : SType Γ) → SType (Γ , τ) → SType Γ
  -- TODO adt

_,`_ : Context → BaseType → Context

data Refinement b Γ where
  _≈_ : ∀ {τ : SType (Γ ,` b)} → STerm (Γ ,` b) τ → STerm (Γ ,` b) τ → Refinement b Γ
  _∧_ : ∀ (ρ₁ ρ₂ : Refinement b Γ) → Refinement b Γ
  ⊤R  : Refinement b Γ

_,`_ Γ b = Γ , ⟨ b ∣ ⊤R ⟩

infix 4 _∈_U_
data _∈_U_ : SType Γ' → (Γ : Context) → Γ' is-prefix-of Γ → Set where
  ∈-zero : ∀ {τ : SType Γ}
         → τ ∈ Γ , τ U is-prefix-of-snoc is-prefix-of-refl
  ∈-suc  : ∀ {τ : SType Γ'}
             {τ' : SType Γ}
             {pref : Γ' is-prefix-of Γ}
         → τ ∈ Γ U pref
         → τ ∈ Γ , τ' U is-prefix-of-snoc pref

weaken-ρ* : Γ' is-prefix-of Γ → Refinement b Γ' → Refinement b Γ
weaken-τ* : Γ' is-prefix-of Γ → SType Γ' → SType Γ

weaken-ρ* is-prefix-of-refl ρ = ρ
weaken-ρ* (is-prefix-of-snoc pref) (x₁ ≈ x₂) = {! !} ≈ {! !}
weaken-ρ* (is-prefix-of-snoc pref) (ρ₁ ∧ ρ₂) = {! !}
weaken-ρ* (is-prefix-of-snoc pref) ⊤R = ⊤R

weaken-τ* is-prefix-of-refl τ = τ
weaken-τ* p@(is-prefix-of-snoc pref) ⟨ b ∣ ρ ⟩ = ⟨ b ∣ weaken-ρ* p ρ ⟩
weaken-τ* (is-prefix-of-snoc pref) (τ₁ ⇒ τ₂) = weaken-τ* (is-prefix-of-snoc pref) τ₁ ⇒ {! !}

data STerm Γ where
  SUnit : STerm Γ ⟨ BUnit ∣ ⊤R ⟩
  SVar  : ∀ {τ : SType Γ'} {pref} → τ ∈ Γ U pref → STerm Γ {! !}
