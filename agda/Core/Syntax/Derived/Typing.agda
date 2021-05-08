{-# OPTIONS --safe #-}

module Core.Syntax.Derived.Typing where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Syntax
open import Core.Syntax.Derived
open import Core.Syntax.Membership
open import Core.Syntax.Renaming
open import Core.Derivations

head-well-formed : Γ , τ ⊢ ε ⦂ τ'
                 → Σ Sort (λ s → Γ ⊢ τ ⦂ CSort s)
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

unweaken : ∀ {sort}
         → Γ , τ₀ ⊢ τ' ⦂ sort
         → τ' ≡ weaken-ε τ
         → CSort s ≡ weaken-ε sort
         → Γ ⊢ τ ⦂ CSort s
unweaken {τ = CVar ι} (CT-Weaken δ δ₁) ≡₁ ≡₂ = {! !}
unweaken {τ = CVar ι} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CSort s} (CT-Weaken δ δ₁) ≡₁ ≡₂ = {! !}
unweaken {τ = CSort s} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CΠ τ τ₁} (CT-Weaken δ δ₁) ≡₁ ≡₂ = {! !}
unweaken {τ = CΠ τ τ₁} (CT-Form δ δ₁) ≡₁ ≡₂ = {! !}
unweaken {τ = CΠ τ τ₁} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CLam τ τ₁} (CT-Weaken δ δ₁) ≡₁ ≡₂ = {! !}
unweaken {τ = CLam τ τ₁} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CApp τ τ₁} (CT-Weaken δ δ₁) ≡₁ ≡₂ = {! !}
unweaken {τ = CApp τ τ₁} (CT-App δ δ₁) ≡₁ ≡₂ = {! !}
unweaken {τ = CApp τ τ₁} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = Cunit} (CT-Weaken δ δ₁) ≡₁ ≡₂ = {! !}
unweaken {τ = Cunit} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CUnit} (CT-Weaken δ δ₁) ≡₁ ≡₂ = {! !}
unweaken {τ = CUnit} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CUnit} (CT-UnitType δ) ≡₁ ≡₂ = {! !}
unweaken {τ = CADT cons} (CT-Weaken δ δ₁) ≡₁ ≡₂ = {! !}
unweaken {τ = CADT cons} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CADT cons} (CT-ADTForm consδs) ≡₁ ≡₂ = {! !}
unweaken {τ = CCon ι τ cons} (CT-Weaken δ δ₁) ≡₁ ≡₂ = {! !}
unweaken {τ = CCon ι τ cons} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CCase τ branches} (CT-Weaken δ δ₁) ≡₁ ≡₂ = {! !}
unweaken {τ = CCase τ branches} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CCase τ branches} (CT-ADTCase δ δ₁ branches₁) ≡₁ ≡₂ = {! !}

CT-VarW : Γ ⊢ τ ⦂ CSort s
        → τ ∈ Γ at ι
        → Γ ⊢ CVar ι ⦂ τ
CT-VarW δ (∈-zero refl) with head-well-formed δ
... | ⟨ _ , δ' ⟩ = CT-Var δ'
CT-VarW δ (∈-suc refl ∈) = let r = CT-VarW {! !} ∈ in {! CT-Weaken !}

⇒'-well-typed : Γ ⊢ τ₁ ⦂ CSort s₁
              → Γ ⊢ τ₂ ⦂ CSort s₂
              → Γ ⊢ (τ₁ ⇒' τ₂) ⦂ CSort s₂
⇒'-well-typed τ₁δ τ₂δ = CT-Form τ₁δ (CT-Weaken τ₂δ τ₁δ)
