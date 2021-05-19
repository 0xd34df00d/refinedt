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

unweaken : Γ , τ₀ ⊢ ε↑ ⦂ τ↑
         → ε↑ ≡ weaken-ε ε
         → τ↑ ≡ weaken-ε τ
         → Γ ⊢ ε ⦂ τ
unweaken (CT-Conv δ₁ δ₂ x) ≡₁ ≡₂
  = CT-Conv (unweaken {! !} refl refl) {! !} {! !} -- unweaken {! !} refl refl -- unweaken δ₁ ≡₁ {! !}
         {-
unweaken {τ = CVar ι} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CSort s} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CΠ τ τ₁} (CT-Form δ δ₁) ≡₁ ≡₂ = {! !}
unweaken {τ = CΠ τ τ₁} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CLam τ τ₁} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CApp τ τ₁} (CT-App δ δ₁) ≡₁ ≡₂ = {! !}
unweaken {τ = CApp τ τ₁} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = Cunit} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CUnit} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CUnit} (CT-UnitType δ) ≡₁ ≡₂ = {! !}
unweaken {τ = CADT cons} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CADT cons} (CT-ADTForm consδs) ≡₁ ≡₂ = {! !}
unweaken {τ = CCon ι τ cons} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CCase τ branches} (CT-Conv δ δ₁ x) ≡₁ ≡₂ = {! !}
unweaken {τ = CCase τ branches} (CT-ADTCase δ δ₁ branches₁) ≡₁ ≡₂ = {! !}
unweaken {τ = τ} {s = s} (CT-Weaken {ε₁ = ε₁} {τ₁ = τ₁} δ _) ≡₁ ≡₂
  rewrite weaken-ε-injective ε₁ τ ≡₁
        | weaken-ε-injective (CSort s) τ₁ (weaken-ε-injective (CSort s) (weaken-ε τ₁) ≡₂)
        = δ
-}

unweaken' : Γ , τ₀ ⊢ weaken-ε ε ⦂ weaken-ε τ
          → Γ ⊢ ε ⦂ τ
unweaken' δ = unweaken δ refl refl

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
... | ⟨ _ , δ' ⟩ = CT-Weaken (CT-VarW (unweaken' δ) ∈) δ'

⇒'-well-typed : Γ ⊢ τ₁ ⦂ CSort s₁
              → Γ ⊢ τ₂ ⦂ CSort s₂
              → Γ ⊢ (τ₁ ⇒' τ₂) ⦂ CSort s₂
⇒'-well-typed τ₁δ τ₂δ = CT-Form τ₁δ (CT-Weaken τ₂δ τ₁δ)
