{-# OPTIONS --safe #-}

module Core.Syntax.Derived.Typing where

open import Data.Fin using (zero; suc)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Syntax
open import Core.Syntax.Derived
open import Core.Syntax.Membership
open import Core.Syntax.Renaming
open import Core.Derivations

head-well-formed : Γ , τ ⊢ ε ⦂ τ'
                 → ∃[ s ] (Γ ⊢ τ ⦂ CSort s)
head-well-formed (CT-Var δ) = ⟨ _ , δ ⟩
head-well-formed (CT-Weaken _ δ) = ⟨ _ , δ ⟩
head-well-formed (CT-Form δ _) = head-well-formed δ
head-well-formed (CT-App _ δ) = head-well-formed δ
head-well-formed (CT-Abs _ δ) = head-well-formed δ
head-well-formed (CT-Conv _ δ _) = head-well-formed δ
head-well-formed (CT-UnitType δ) = head-well-formed δ
head-well-formed (CT-UnitTerm δ) = head-well-formed δ
head-well-formed (CT-ADTForm (δ ∷ _)) = head-well-formed δ
head-well-formed (CT-ADTCon _ _ δ) = head-well-formed δ
head-well-formed (CT-ADTCase _ δ _) = head-well-formed δ

τ∈Γ-wf : Γ ⊢ τ' ⦂ CSort s'
       → τ ∈ Γ at ι
       → ∃[ s ] (Γ ⊢ τ ⦂ CSort s)
τ∈Γ-wf δ (∈-zero refl) with head-well-formed δ
... | ⟨ s , δ' ⟩ = ⟨ s , CT-Weaken δ' δ' ⟩
τ∈Γ-wf δ (∈-suc refl ∈) with head-well-formed δ
... | ⟨ s' , δ' ⟩ with τ∈Γ-wf δ' ∈
...   | ⟨ s , δ₀ ⟩ = ⟨ s , CT-Weaken δ₀ δ' ⟩

CT-VarW : Γ ⊢ τ ⦂ CSort s
        → τ ∈ Γ at ι
        → Γ ⊢ CVar ι ⦂ τ
CT-VarW δ (∈-zero refl) with head-well-formed δ
... | ⟨ _ , δ' ⟩ = CT-Var δ'
CT-VarW δ (∈-suc refl ∈) with head-well-formed δ
... | ⟨ _ , δ' ⟩ with τ∈Γ-wf δ' ∈
...   | ⟨ _ , δ'' ⟩ = CT-Weaken (CT-VarW δ'' ∈) δ'

⇒'-well-typed : Γ ⊢ τ₁ ⦂ CSort s₁
              → Γ ⊢ τ₂ ⦂ CSort s₂
              → Γ ⊢ (τ₁ ⇒' τ₂) ⦂ CSort s₂
⇒'-well-typed τ₁δ τ₂δ = CT-Form τ₁δ (CT-Weaken τ₂δ τ₁δ)

Γ⊢⋆⦂□ : Γ ⊢ ε ⦂ τ
      → Γ ⊢ ⋆ₑ ⦂ □ₑ
Γ⊢⋆⦂□ {Γ = ⊘} _ = CT-Sort
Γ⊢⋆⦂□ {Γ = Γ , τ} δ with head-well-formed δ
... | ⟨ _ , δ' ⟩ = CT-Weaken (Γ⊢⋆⦂□ δ') δ'

Σ-cont-well-typed : ∀ {Γ : Ctx ℓ} {P}
                  → Γ ⊢ τ ⦂ CSort s
                  → Γ ⊢ P ⦂ τ ⇒' ⋆ₑ
                  → Γ , ⋆ₑ ⊢ CΠ (weaken-ε τ) (CApp (weaken-ε (weaken-ε P)) (CVar zero) ⇒' CVar (suc zero)) ⦂ ⋆ₑ
Σ-cont-well-typed δτ δP =
  let Γ,⋆⊢τ = CT-Weaken δτ (Γ⊢⋆⦂□ δτ)
   in CT-Form
        Γ,⋆⊢τ
        (⇒'-well-typed
          (CT-App
            (CT-Weaken
              (CT-Weaken δP (Γ⊢⋆⦂□ δτ))
              Γ,⋆⊢τ
            )
            (CT-Var Γ,⋆⊢τ)
          )
          (CT-Weaken (CT-Var (Γ⊢⋆⦂□ δτ)) Γ,⋆⊢τ)
        )

Σ-well-typed : ∀ {Γ : Ctx ℓ} {P}
             → Γ ⊢ τ ⦂ CSort s
             → Γ ⊢ P ⦂ τ ⇒' ⋆ₑ
             → Γ ⊢ Σ[ τ ] P ⦂ ⋆ₑ
Σ-well-typed δ₁ δ₂ =
  CT-Form
    (Γ⊢⋆⦂□ δ₁)
    (CT-Form
      (Σ-cont-well-typed δ₁ δ₂)
      (CT-Weaken (CT-Var (Γ⊢⋆⦂□ δ₁)) (Σ-cont-well-typed δ₁ δ₂))
    )

×-well-typed : Γ ⊢ τ₁ ⦂ ⋆ₑ
             → Γ ⊢ τ₂ ⦂ ⋆ₑ
             → Γ ⊢ ⟨ τ₁ × τ₂ ⟩ ⦂ ⋆ₑ
×-well-typed δ₁ δ₂ =
  Σ-well-typed
    δ₁
    (CT-Abs
      (CT-Weaken δ₂ δ₁)
      (CT-Form δ₁ (CT-Weaken (Γ⊢⋆⦂□ δ₁) δ₁))
    )

≡̂-well-typed : Γ ⊢ ε₁ ⦂ τ
             → Γ ⊢ ε₂ ⦂ τ
             → Γ ⊢ τ ⦂ ⋆ₑ
             → Γ ⊢ ε₁ ≡̂ ε₂ of τ ⦂ ⋆ₑ
≡̂-well-typed {_} {Γ} {ε₁} {τ} {ε₂} ε₁δ ε₂δ τδ =
  CT-Form
    Γ⊢τ⇒'⋆ₑ
    (×-well-typed ε₁⇒ε₂ ε₂⇒ε₁)
  where
  Γ⊢τ⇒'⋆ₑ : Γ ⊢ τ ⇒' ⋆ₑ ⦂ □ₑ
  Γ⊢τ⇒'⋆ₑ = ⇒'-well-typed τδ (Γ⊢⋆⦂□ τδ)

  ε₁⇒ε₂ : Γ , (τ ⇒' ⋆ₑ) ⊢ (CVar zero · weaken-ε ε₁) ⇒' (CVar zero · weaken-ε ε₂) ⦂ ⋆ₑ
  ε₁⇒ε₂ = ⇒'-well-typed
            (CT-App (CT-Var Γ⊢τ⇒'⋆ₑ) (CT-Weaken ε₁δ Γ⊢τ⇒'⋆ₑ))
            (CT-App (CT-Var Γ⊢τ⇒'⋆ₑ) (CT-Weaken ε₂δ Γ⊢τ⇒'⋆ₑ))

  ε₂⇒ε₁ : Γ , (τ ⇒' ⋆ₑ) ⊢ (CVar zero · weaken-ε ε₂) ⇒' (CVar zero · weaken-ε ε₁) ⦂ ⋆ₑ
  ε₂⇒ε₁ = ⇒'-well-typed
            (CT-App (CT-Var Γ⊢τ⇒'⋆ₑ) (CT-Weaken ε₂δ Γ⊢τ⇒'⋆ₑ))
            (CT-App (CT-Var Γ⊢τ⇒'⋆ₑ) (CT-Weaken ε₁δ Γ⊢τ⇒'⋆ₑ))
