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
open import Misc.Helpers

infix 19 _,_
_,_ : Ctx → Ctx → Ctx
_,_ Γ Δ = Δ ++ Γ

exchange-Γok   : Γ ⊢ τ₂ → ∀ Δ → (Γ , x₁ ⦂ τ₁ , x₂ ⦂ τ₂ , Δ) ok → (Γ , x₂ ⦂ τ₂ , x₁ ⦂ τ₁ , Δ) ok
exchange-Γ⊢τ   : Γ ⊢ τ₂ → ∀ Δ → (Γ , x₁ ⦂ τ₁ , x₂ ⦂ τ₂ , Δ) ⊢ τ → (Γ , x₂ ⦂ τ₂ , x₁ ⦂ τ₁ , Δ) ⊢ τ
exchange-Γ⊢ε⦂τ : Γ ⊢ τ₂ → ∀ Δ → (Γ , x₁ ⦂ τ₁ , x₂ ⦂ τ₂ , Δ) ⊢ ε ⦂ τ → (Γ , x₂ ⦂ τ₂ , x₁ ⦂ τ₁ , Δ) ⊢ ε ⦂ τ

exchange-Γok no-x [] (TCTX-Bind (TCTX-Bind prevOk τδ₁) τδ₂) = TCTX-Bind (TCTX-Bind prevOk no-x) (twf-weakening prevOk no-x τδ₁)
exchange-Γok no-x ((x ,' τ) ∷ Δ) (TCTX-Bind δ τδ) = TCTX-Bind (exchange-Γok no-x Δ δ) (exchange-Γ⊢τ no-x Δ τδ)

exchange-Γ⊢τ no-x Δ (TWF-TrueRef gok) = TWF-TrueRef (exchange-Γok no-x Δ gok)
exchange-Γ⊢τ no-x Δ (TWF-Base ε₁δ ε₂δ) = TWF-Base (exchange-Γ⊢ε⦂τ no-x (_ ∷ Δ) ε₁δ) (exchange-Γ⊢ε⦂τ no-x (_ ∷ Δ) ε₂δ)
exchange-Γ⊢τ no-x Δ (TWF-Conj ρ₁δ ρ₂δ) = TWF-Conj (exchange-Γ⊢τ no-x Δ ρ₁δ) (exchange-Γ⊢τ no-x Δ ρ₂δ)
exchange-Γ⊢τ no-x Δ (TWF-Arr argδ resδ) = TWF-Arr (exchange-Γ⊢τ no-x Δ argδ) (exchange-Γ⊢τ no-x (_ ∷ Δ) resδ)
exchange-Γ⊢τ {Γ = Γ} {τ₂ = τ₂} no-x Δ (TWF-ADT consδs) = TWF-ADT (exchange-cons consδs)
  where
    exchange-cons : {cons : ADTCons n} → All ((Γ , x₁ ⦂ τ₁ , x₂ ⦂ τ₂ , Δ) ⊢_) cons → All ((Γ , x₂ ⦂ τ₂ , x₁ ⦂ τ₁ , Δ) ⊢_) cons
    exchange-cons [] = []
    exchange-cons (px ∷ pxs) = exchange-Γ⊢τ no-x Δ px ∷ exchange-cons pxs

exchange-Γ⊢ε⦂τ no-x Δ (T-Unit gok) = T-Unit (exchange-Γok no-x Δ gok)
exchange-Γ⊢ε⦂τ no-x Δ (T-Var gok ∈) = T-Var (exchange-Γok no-x Δ gok) (∈-swap ∈)
exchange-Γ⊢ε⦂τ no-x Δ (T-Abs arrδ bodyδ) = T-Abs (exchange-Γ⊢τ no-x Δ arrδ) (exchange-Γ⊢ε⦂τ no-x (_ ∷ Δ) bodyδ)
exchange-Γ⊢ε⦂τ no-x Δ (T-App δ₁ δ₂) = T-App (exchange-Γ⊢ε⦂τ no-x Δ δ₁) (exchange-Γ⊢ε⦂τ no-x Δ δ₂)
exchange-Γ⊢ε⦂τ no-x Δ (T-Case resδ δ branches) = T-Case (exchange-Γ⊢τ no-x Δ resδ) (exchange-Γ⊢ε⦂τ no-x Δ δ) {! !}
exchange-Γ⊢ε⦂τ no-x Δ (T-Con conArg adtτ) = T-Con (exchange-Γ⊢ε⦂τ no-x Δ conArg) (exchange-Γ⊢τ no-x Δ adtτ)
exchange-Γ⊢ε⦂τ no-x Δ (T-Sub δ sub) = T-Sub (exchange-Γ⊢ε⦂τ no-x Δ δ) {! !}
