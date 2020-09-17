module Surface.Theorems where

open import Data.List.Base using (_++_)
open import Data.Product renaming (_,_ to _,'_)

open import Surface.Syntax
open import Surface.Derivations
open import Surface.Derivations.WF
open import Surface.Theorems.TCTX
open import Surface.Theorems.Helpers
open import Surface.Theorems.Thinning

open import Sublist

infix 19 _,_
_,_ : Ctx → Ctx → Ctx
_,_ Γ Δ = Δ ++ Γ

exchange-Γok   : ∀ {Δ} → Γ ⊢ τ₂ → (Γ , x₁ ⦂ τ₁ , x₂ ⦂ τ₂ , Δ) ok → (Γ , x₂ ⦂ τ₂ , x₁ ⦂ τ₁ , Δ) ok
exchange-Γ⊢τ   : ∀ {Δ} → Γ ⊢ τ₂ → (Γ , x₁ ⦂ τ₁ , x₂ ⦂ τ₂ , Δ) ⊢ τ → (Γ , x₂ ⦂ τ₂ , x₁ ⦂ τ₁ , Δ) ⊢ τ
exchange-Γ⊢ε⦂τ : ∀ {Δ} → Γ ⊢ τ₂ → (Γ , x₁ ⦂ τ₁ , x₂ ⦂ τ₂ , Δ) ⊢ ε ⦂ τ → (Γ , x₂ ⦂ τ₂ , x₁ ⦂ τ₁ , Δ) ⊢ ε ⦂ τ

exchange-Γok {Δ = []} no_x (TCTX-Bind (TCTX-Bind prevOk τδ₁) τδ₂) = TCTX-Bind (TCTX-Bind prevOk no_x) (twf-weakening prevOk no_x τδ₁)
exchange-Γok {Δ = (x ,' τ) ∷ Δ} no_x (TCTX-Bind δ τδ) = TCTX-Bind (exchange-Γok no_x δ) (exchange-Γ⊢τ no_x τδ)
