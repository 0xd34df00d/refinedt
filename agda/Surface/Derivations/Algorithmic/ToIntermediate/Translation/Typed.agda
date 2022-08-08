{-# OPTIONS --allow-unsolved-metas #-}

module Surface.Derivations.Algorithmic.ToIntermediate.Translation.Typed where

open import Data.Fin using (suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax as S
open import Surface.Derivations.Algorithmic as S

open import Intermediate.Syntax as I
open import Intermediate.Syntax.Short
open import Intermediate.Syntax.Renaming as IR
open import Intermediate.Derivations.Algorithmic as I

open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Aliases

μ-b : S.BaseType → I.BaseType
μ-b BUnit = BUnit

mutual
  μ-ρ : {ρˢ : Refinement (suc ℓ)}
      → Γˢ ⊢[ θˢ , E ] ⟨ bˢ ∣ ρˢ ⟩
      → IRefinement (suc ℓ)
  μ-ρ (TWF-TrueRef _) = Τ
  μ-ρ (TWF-Base {b' = b'ˢ} ε₁δ ε₂δ) = μ-ε ε₁δ ≈ μ-ε ε₂δ of ⟨ μ-b b'ˢ ∣ Τ ⟩
  μ-ρ (TWF-Conj τ₁δ τ₂δ) = μ-ρ τ₁δ ∧ μ-ρ τ₂δ

  μ-τ : {τˢ : SType ℓ}
      → Γˢ ⊢[ θˢ , E ] τˢ
      → IType ℓ
  μ-τ {τˢ = ⟨ b ∣ ρ ⟩} τδ = ⟨ μ-b b ∣ μ-ρ τδ ⟩
  μ-τ {τˢ = _ ⇒ _} (TWF-Arr τ₁δ τ₂δ) = μ-τ τ₁δ ⇒ μ-τ τ₂δ
  μ-τ {τˢ = ⊍ cons} τδ = {! !}

  μ-ε : {τˢ : SType ℓ}
      → Γˢ ⊢[ θˢ , E of κ ] εˢ ⦂ τˢ
      → ITerm ℓ
  μ-ε (T-Unit _) = IUnit
  μ-ε (T-Var {ι = ι} _ _) = IVar ι
  μ-ε (T-Abs εδ ⦃ enriched (TWF-Arr τ₁δ _) ⦄) = ƛ μ-τ τ₁δ ⇉ μ-ε εδ
  μ-ε (T-App ε₁δ ε₂δ _) = μ-ε ε₁δ ∙ μ-ε ε₂δ
  μ-ε (T-Case resδ εδ bsδ) = {! !}
  μ-ε (T-Con <:δ εδ adtτ) = {! !}
  μ-ε (T-Sub εδ <:δ ⦃ enriched τδ ⦄) = μ-<: <:δ ∙ μ-ε εδ

  {-
  A witness of τ' <: τ gets converted to a function τ' ⇒ τ.

  For the base case of a base value, we produce the syntactic witness of subtyping
  that'll be handled by the intermediate oracle later on.

  For the function case, we have τ₁ ⇒ τ₂' <: τ₁' ⇒ τ₂ and we translate it to a function
  λ τ₁ ⇒ τ₂'.
    λ τ₁'.
      <:₂ⁱ (#1 (<:₁ⁱ #0)).
  -}
  μ-<: : {τˢ : SType ℓ}
       → Γˢ ⊢[ θˢ , E ] τ'ˢ <: τˢ
       → ITerm ℓ
  μ-<: (ST-Base is-just) = {! !}
  μ-<: (ST-Arr <:₁δ <:₂δ ⦃ enriched τ₁⇒τ₂'δ ⦄ ⦃ enriched (TWF-Arr τ₁'δ _) ⦄)
    = let <:₁ⁱ = IR.weaken-ε-k _ (μ-<: <:₁δ)
          <:₂ⁱ = IR.weaken-ε (μ-<: <:₂δ)
          τ₁⇒τ₂'ⁱ = μ-τ τ₁⇒τ₂'δ
          τ₁'ⁱ = IR.weaken-τ (μ-τ τ₁'δ)
       in ƛ τ₁⇒τ₂'ⁱ ⇉
            ƛ τ₁'ⁱ ⇉
              <:₂ⁱ ∙ (# 1 ∙ (<:₁ⁱ ∙ # 0))
  μ-<: (ST-ADT _) = {! !}

μ-Γ : {Γˢ : S.Ctx ℓ}
    → Γˢ ok[ θˢ , E ]
    → I.Ctx ℓ
μ-Γ TCTX-Empty = ⊘
μ-Γ (TCTX-Bind Γok τδ) = μ-Γ Γok , μ-τ τδ
