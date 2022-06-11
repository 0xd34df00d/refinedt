module Surface.Derivations.Algorithmic.ToIntermediate.Translation where

open import Data.Fin using (suc; zero; #_)

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
open import Intermediate.Syntax.Renaming as IR
open import Intermediate.Derivations.Algorithmic as I renaming (θ to θⁱ)

mutual
  μ-τ : {τˢ : SType ℓ}
      → Γˢ ⊢[ θˢ , E ] τˢ
      → IType ℓ
  μ-τ τδ = {! !}

  μ-ε : {τˢ : SType ℓ}
      → Γˢ ⊢[ θˢ , E of κ ] εˢ ⦂ τˢ
      → ITerm ℓ
  μ-ε (T-Unit _) = IUnit
  μ-ε (T-Var {ι = ι} _ _) = IVar ι
  μ-ε (T-Abs (TWF-Arr τ₁δ τ₂δ) εδ) = ILam (μ-τ τ₁δ) (μ-ε εδ)
  μ-ε (T-App ε₁δ ε₂δ _ _) = IApp (μ-ε ε₁δ) (μ-ε ε₂δ)
  μ-ε (T-Case resδ εδ branches-well-typed) = {! !}
  μ-ε (T-Con ≡-prf εδ adtτ) = {! !}
  μ-ε (T-Sub εδ _ <:δ) = IApp (μ-ε εδ) (μ-<: <:δ)

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
    = let <:₁ⁱ = μ-<: <:₁δ
          <:₂ⁱ = μ-<: <:₂δ
       in ILam (μ-τ τ₁⇒τ₂'δ)
            (ILam (IR.weaken-τ (μ-τ τ₁'δ))
              (IApp
                (IR.weaken-ε <:₂ⁱ)
                (IApp
                  (IVar (# 1))
                  (IApp
                    (weaken-ε-k _ <:₁ⁱ)
                    (IVar (# 0))
                  )
                )
              )
            )
