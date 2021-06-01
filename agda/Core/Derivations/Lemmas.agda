{-# OPTIONS --safe #-}

module Core.Derivations.Lemmas where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Syntax
open import Core.Syntax.Membership
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

Γ⊢⋆⦂□ : Γ ⊢ ε ⦂ τ
      → Γ ⊢ ⋆ₑ ⦂ □ₑ
Γ⊢⋆⦂□ {Γ = ⊘} _ = CT-Sort
Γ⊢⋆⦂□ {Γ = Γ , τ} δ with head-well-formed δ
... | ⟨ _ , δ' ⟩ = CT-Weaken (Γ⊢⋆⦂□ δ') δ'

Γ⊢τ-⇒-Γ,τ-ok : Γ ⊢ τ ⦂ CSort s
             → Γ , τ ⊢ ⋆ₑ ⦂ □ₑ
Γ⊢τ-⇒-Γ,τ-ok δτ = CT-Weaken (Γ⊢⋆⦂□ δτ) δτ

Γ,τ-ok-⇒-Γ-ok : Γ , τ ⊢ ⋆ₑ ⦂ □ₑ
              → Γ ⊢ ⋆ₑ ⦂ □ₑ
Γ,τ-ok-⇒-Γ-ok δ with head-well-formed δ
... | ⟨ _ , δ' ⟩ = Γ⊢⋆⦂□ δ'
