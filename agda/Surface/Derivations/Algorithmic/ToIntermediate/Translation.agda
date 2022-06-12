module Surface.Derivations.Algorithmic.ToIntermediate.Translation where

open import Data.Fin using (suc; zero)

open import Surface.Syntax as S renaming (Γ to Γˢ;
                                          τ to τˢ; τ' to τ'ˢ; σ to σˢ;
                                          τ₁ to τ₁ˢ; τ₁' to τ₁'ˢ;
                                          τ₂ to τ₂ˢ; τ₂' to τ₂'ˢ;
                                          ε to εˢ; ε' to ε'ˢ; ε₁ to ε₁ˢ; ε₂ to ε₂ˢ)
open import Surface.Derivations.Algorithmic as S renaming (θ to θˢ)

open import Intermediate.Syntax as I renaming (Γ to Γⁱ;
                                               τ to τⁱ; τ' to τ'ⁱ; σ to σⁱ;
                                               τ₁ to τ₁ⁱ; τ₁' to τ₁'ⁱ;
                                               τ₂ to τ₂ⁱ; τ₂' to τ₂'ⁱ;
                                               ε to εⁱ; ε' to ε'ⁱ; ε₁ to ε₁ⁱ; ε₂ to ε₂ⁱ)
open import Intermediate.Syntax.Short
open import Intermediate.Syntax.Renaming as IR
open import Intermediate.Derivations.Algorithmic as I renaming (θ to θⁱ)

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
  μ-ε (T-Abs (TWF-Arr τ₁δ τ₂δ) εδ) = ƛ μ-τ τ₁δ ⇉ μ-ε εδ
  μ-ε (T-App ε₁δ ε₂δ _ _) = μ-ε ε₁δ ∙ μ-ε ε₂δ
  μ-ε (T-Case resδ εδ branches-well-typed) = {! !}
  μ-ε (T-Con ≡-prf εδ adtτ) = {! !}
  μ-ε (T-Sub εδ _ <:δ) = μ-ε εδ ∙ μ-<: <:δ

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
  μ-<: (ST-Arr <:₁δ <:₂δ (enriched τ₁⇒τ₂'δ) (enriched τ₁'δ))
    = let <:₁ⁱ = IR.weaken-ε-k _ (μ-<: <:₁δ)
          <:₂ⁱ = IR.weaken-ε (μ-<: <:₂δ)
          τ₁⇒τ₂'ⁱ = μ-τ τ₁⇒τ₂'δ
          τ₁'ⁱ = IR.weaken-τ (μ-τ τ₁'δ)
       in ƛ τ₁⇒τ₂'ⁱ ⇉
            ƛ τ₁'ⁱ ⇉
              <:₂ⁱ ∙ (# 1 ∙ (<:₁ⁱ ∙ # 0))

μ-Γ : {Γˢ : S.Ctx ℓ}
    → Γˢ ok[ θˢ , E ]
    → I.Ctx ℓ
μ-Γ TCTX-Empty = ⊘
μ-Γ (TCTX-Bind Γok τδ) = μ-Γ Γok , μ-τ τδ
