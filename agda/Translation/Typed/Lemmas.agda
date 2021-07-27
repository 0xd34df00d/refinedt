-- {-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Translation.Typed.Lemmas where

open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Syntax as C
open import Core.Syntax.Derived as C
open import Core.Syntax.Renaming as CR
open import Core.Derivations as C renaming (_⊢_⦂_ to _⊢ᶜ_⦂_)
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; ε to εˢ)
open import Surface.Derivations as S renaming (_⊢_⦂_ to _⊢ˢ_⦂_)
open import Translation.Untyped
open import Translation.Typed

μ-b≡μ-τ[Γ⊢b] : (δ : Γˢ ⊢ ⟨ b ∣ Τ ⟩)
             → ⌊μ⌋-b b ≡ μ-τ δ
μ-b≡μ-τ[Γ⊢b] {b = BUnit} (TWF-TrueRef _) = refl

μ-τ-equiv : (δ₁ δ₂ : Γˢ ⊢ τˢ)
          → μ-τ δ₁ ≡ μ-τ δ₂
μ-τ-equiv (TWF-TrueRef _) (TWF-TrueRef _) = refl
μ-τ-equiv (TWF-Base ε₁δ₁ ε₂δ₁) (TWF-Base ε₁δ₂ ε₂δ₂) = {! !}
μ-τ-equiv (TWF-Conj δ₁ δ₂) (TWF-Conj δ₃ δ₄) = {! !}
μ-τ-equiv (TWF-Arr δ₁ δ₂) (TWF-Arr δ₃ δ₄) = {! !}
μ-τ-equiv (TWF-ADT consδs) (TWF-ADT consδs₁) = {! !}

μ-ε-equiv : (δ₁ δ₂ : Γˢ ⊢ˢ εˢ ⦂ τˢ)
          → μ-ε δ₁ ≡ μ-ε δ₂
μ-ε-equiv (T-Unit Γok) (T-Unit Γok₁) = refl
μ-ε-equiv (T-Unit Γok) (T-Sub δ₂ τ'δ <:) = {! <: !}
μ-ε-equiv (T-Unit Γok) (T-RConv δ₂ τ'δ τ~τ') = {! !}
μ-ε-equiv (T-Var Γok x) δ₂ = {! !}
μ-ε-equiv (T-Abs arrδ δ₁) δ₂ = {! !}
μ-ε-equiv (T-App δ₁ δ₃) δ₂ = {! !}
μ-ε-equiv (T-Case resδ δ₁ branches-well-typed) δ₂ = {! !}
μ-ε-equiv (T-Con ≡-prf δ₁ adtτ) δ₂ = {! !}
μ-ε-equiv (T-Sub δ₁ τ'δ <:) δ₂ = {! !}
μ-ε-equiv (T-RConv δ₁ τ'δ τ~τ') δ₂ = {! !}

μ-Γ-cong : (Γok₁ Γok₂ : Γˢ ok)
         → μ-Γ Γok₁ ⊢ᶜ ε ⦂ τ
         → μ-Γ Γok₂ ⊢ᶜ ε ⦂ τ
μ-Γ-cong TCTX-Empty TCTX-Empty δ = δ
μ-Γ-cong (TCTX-Bind Γok₁ τδ₁) (TCTX-Bind Γok₂ τδ₂) (CT-Var δ) = let r = CT-Var (μ-Γ-cong Γok₁ Γok₂ δ) in {! !}
μ-Γ-cong (TCTX-Bind Γok₁ τδ₁) (TCTX-Bind Γok₂ τδ₂) (CT-Weaken δ δ₁) = CT-Weaken (μ-Γ-cong Γok₁ Γok₂ δ) {! !}
μ-Γ-cong (TCTX-Bind Γok₁ τδ₁) (TCTX-Bind Γok₂ τδ₂) (CT-Form δ δ₁) = {! !}
μ-Γ-cong (TCTX-Bind Γok₁ τδ₁) (TCTX-Bind Γok₂ τδ₂) (CT-App δ δ₁) = {! !}
μ-Γ-cong (TCTX-Bind Γok₁ τδ₁) (TCTX-Bind Γok₂ τδ₂) (CT-Abs δ δ₁) = {! !}
μ-Γ-cong (TCTX-Bind Γok₁ τδ₁) (TCTX-Bind Γok₂ τδ₂) (CT-Conv δ δ₁ x) = {! !}
μ-Γ-cong (TCTX-Bind Γok₁ τδ₁) (TCTX-Bind Γok₂ τδ₂) (CT-UnitType δ) = CT-UnitType (μ-Γ-cong (TCTX-Bind Γok₁ τδ₁) (TCTX-Bind Γok₂ τδ₂) δ)
μ-Γ-cong (TCTX-Bind Γok₁ τδ₁) (TCTX-Bind Γok₂ τδ₂) (CT-UnitTerm δ) = CT-UnitTerm (μ-Γ-cong (TCTX-Bind Γok₁ τδ₁) (TCTX-Bind Γok₂ τδ₂) δ)
μ-Γ-cong (TCTX-Bind Γok₁ τδ₁) (TCTX-Bind Γok₂ τδ₂) (CT-ADTForm consδs) = {! !}
μ-Γ-cong (TCTX-Bind Γok₁ τδ₁) (TCTX-Bind Γok₂ τδ₂) (CT-ADTCon ≡-prf δ δ₁) = {! !}
μ-Γ-cong (TCTX-Bind Γok₁ τδ₁) (TCTX-Bind Γok₂ τδ₂) (CT-ADTCase δ δ₁ branches) = {! !}
