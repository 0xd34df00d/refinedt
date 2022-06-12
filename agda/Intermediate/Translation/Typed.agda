{-# OPTIONS --safe #-}

module Intermediate.Translation.Typed where

open import Data.Fin using (zero; suc)
open import Data.Maybe using (Is-just; just; to-witness)
open import Data.Vec using (_∷_; [])

open import Core.Syntax as C
open import Core.Syntax.Derived as C
open import Core.Syntax.Renaming as C
open import Core.Derivations as C
open import Intermediate.Syntax as I renaming (Γ to Γⁱ; τ to τⁱ; ε to εⁱ)
open import Intermediate.Syntax.CtxSuffix
open import Intermediate.Derivations.Algorithmic as I renaming ([_]_⊢_⦂_ to [_]_⊢ⁱ_⦂_)

open import Intermediate.Translation.Untyped

mutual
  {-
  A witness of
  τ' <: τ
  gets translated to a function of type
  τ' ⇒ τ
  -}
  μ-<: : {τ' τ : IType ℓ}
       → [ θ ] Γⁱ ⊢ τ' <: τ
       → CExpr ℓ
  μ-<: (ST-Base positive _ _) = PositiveDecision.<:-ε (to-witness positive)
  μ-<: (ST-Arr <:₁δ <:₂δ τ₁⇒τ₂'δ (TWF-Arr τ₁'δ _))
    {-
    Here, τ' ~ τ₁  ⇒ τ₂'
          τ  ~ τ₁' ⇒ τ₂
    and we need to build a function of type (τ₁ ⇒ τ₂') ⇒ (τ₁' ⇒ τ₂)

    Thus, we do the following:
    λ (τ₁ ⇒ τ₂').
      λ τ₁'.
        μ(<:₂δ)
          (#1
            (μ(<:₁δ) (#0)))
    -}
    = let arg-ε = μ-<: <:₁δ  -- ⦂ τ₁' ⇒ τ₁
          res-ε = μ-<: <:₂δ  -- ⦂ τ₂' ⇒ τ₂
       in CLam
            (μ-τ τ₁⇒τ₂'δ)
            (CLam
              (weaken-ε (μ-τ τ₁'δ))
              (act-ε (ext suc) res-ε ·
                (CVar (suc zero) ·
                  (weaken-ε-k 2 arg-ε · CVar zero)))
            )

  μ-τ : {τ : IType ℓ}
      → [ θ ] Γⁱ ⊢ τ
      → CExpr ℓ
  μ-τ (TWF-TrueRef {b = b} Γok) = ⌊μ⌋-b b
  μ-τ (TWF-Base {b = b} {b' = b'} ε₁δ ε₂δ)
    = let b̂ = ⌊μ⌋-b b
       in Σ[ b̂ ] CLam b̂ (μ-ε ε₁δ ≡̂ μ-ε ε₂δ of ⌊μ⌋-b b')
  μ-τ (TWF-Conj δ₁ δ₂) = ⟨ μ-τ δ₁ × μ-τ δ₂ ⟩ -- TODO isn't this obviously wrong?
  μ-τ (TWF-Arr τ₁δ τ₂δ) = CΠ (μ-τ τ₁δ) (μ-τ τ₂δ)
  μ-τ (TWF-ADT consδs) = CADT (μ-cons consδs)

  μ-ε : ∀ {ε : ITerm ℓ} {τ}
      → [ θ ] Γⁱ ⊢ⁱ ε ⦂ τ
      → CExpr ℓ
  μ-ε (T-Unit Γok) = [ Cunit ⦂ CUnit ∣ eq-refl CUnit Cunit of CLam CUnit ⌊μ⌋-Τ ]
  μ-ε (T-Var {ι = ι} _ _) = CVar ι
  μ-ε (T-Abs (TWF-Arr domδ _) εδ) = CLam (μ-τ domδ) (μ-ε εδ)
  μ-ε (T-App ε₁δ ε₂δ _ _) = μ-ε ε₁δ · μ-ε ε₂δ
  μ-ε (T-Case resδ εδ branches) = CCase (μ-ε εδ) (μ-branches branches)
  μ-ε (T-Con {ι = ι} _ εδ (TWF-ADT adtτ)) = CCon ι (μ-ε εδ) (μ-cons adtτ)
  μ-ε (T-SubW <: εδ) = μ-<: <: · μ-ε εδ

  μ-cons : {cons : I.ADTCons nₐ ℓ}
         → All ([ θ ] Γⁱ ⊢_) cons
         → C.ADTCons nₐ ℓ
  μ-cons [] = []
  μ-cons (τδ ∷ consδ) = μ-τ τδ ∷ μ-cons consδ

  μ-branches : {branches : I.CaseBranches nₐ ℓ}
             → {cons : I.ADTCons nₐ ℓ}
             → I.BranchesHaveType θ Γⁱ cons branches τⁱ
             → C.CaseBranches nₐ ℓ
  μ-branches NoBranches = []
  μ-branches (OneMoreBranch εδ bs) = {- TODO placeholder proper proof -} Cunit ∷ μ-branches bs

μ-Γ : {Γⁱ : I.Ctx ℓ}
    → [ θ ] Γⁱ ok
    → C.Ctx ℓ
μ-Γ TCTX-Empty = ⊘
μ-Γ (TCTX-Bind Γok τδ) = μ-Γ Γok , μ-τ τδ
