module Surface.Derivations.Algorithmic.ToIntermediate.Translation where

open import Data.Fin using (suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax as S
import Surface.Syntax.Membership as S
import Surface.Syntax.Substitution as S
open import Surface.Derivations.Algorithmic as S
open import Surface.Derivations.Algorithmic.Theorems.Agreement

open import Intermediate.Syntax as I
open import Intermediate.Syntax.Short
open import Intermediate.Syntax.Renaming as IR
import Intermediate.Derivations.Algorithmic as I

open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Aliases
open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Subst
open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Typed

mutual
  μ-ε-δ : {τˢ : SType ℓ}
        → (εδ : Γˢ ⊢[ θˢ , E of κ ] εˢ ⦂ τˢ)
        → [ θⁱ ] μ-Γ (Γ⊢ε⦂τ-⇒-Γok εδ) ⊢ μ-ε εδ ⦂ μ-τ (Γ⊢ε⦂τ-⇒-Γ⊢τ εδ)
  μ-ε-δ (T-Unit Γok) = T-Unit {! !}
  μ-ε-δ (T-Var Γok ∈) = T-Var {! !} {! !}
  μ-ε-δ (T-Abs τ₁⇒τ₂δ@(TWF-Arr τ₁δ τ₂δ) εδ)
    = let εδⁱ = μ-ε-δ εδ
          εδⁱ = subst-Γ⊢ε⦂[τ] _ τ₂δ εδⁱ
          εδⁱ = subst-[Γ]⊢ε⦂τ _ _   εδⁱ
       in T-Abs (μ-τ-δ τ₁⇒τ₂δ) εδⁱ
  μ-ε-δ (T-App ε₁δ ε₂δ refl resτδ)
    = {! !}
  μ-ε-δ (T-Case resδ εδ branches-well-typed) = {! !}
  μ-ε-δ (T-Con ≡-prf εδ adtτ) = {! !}
  μ-ε-δ (T-Sub εδ τ'δ <:δ) = {! !}
  {-
    = let εδⁱ = μ-ε-δ εδ
       in T-App {! !} {! !} {! refl !} {! !}
       -}

  μ-τ-δ : {τˢ : SType ℓ}
        → (τδ : Γˢ ⊢[ θˢ , E ] τˢ)
        → [ θⁱ ] μ-Γ (Γ⊢τ-⇒-Γok τδ) ⊢ μ-τ τδ
  μ-τ-δ τδ = {! !}

  μ-Γ-δ : (Γok : Γˢ ok[ θˢ , E ])
        → [ θⁱ ] μ-Γ Γok ok
  μ-Γ-δ TCTX-Empty = TCTX-Empty
  μ-Γ-δ (TCTX-Bind Γok τδ) = TCTX-Bind (μ-Γ-δ Γok) (subst-[Γ]⊢τ _ _ (μ-τ-δ τδ))
