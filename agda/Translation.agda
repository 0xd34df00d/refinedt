{-# OPTIONS --safe #-}

module Translation where

open import Core.Syntax as C
open import Core.Derivations as C
open import Surface.Syntax as S
open import Surface.Derivations as S

μ-Γ : {Γ : S.Ctx ℓ}
    → Γ ok
    → C.Ctx ℓ
μ-τ : {Γ : S.Ctx ℓ}
    → {τ : SType ℓ}
    → Γ ⊢ τ
    → CExpr ℓ

μ-Γ TCTX-Empty = ⊘
μ-Γ (TCTX-Bind Γok τδ) = μ-Γ Γok , μ-τ τδ

μ-τ (TWF-TrueRef Γok) = {! !}
μ-τ (TWF-Base ε₁δ ε₂δ) = {! !}
μ-τ (TWF-Conj ρ₁δ ρ₂δ) = {! !}
μ-τ (TWF-Arr argδ resδ) = {! !}
μ-τ (TWF-ADT consδs) = {! !}
