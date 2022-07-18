{-# OPTIONS --safe #-}

module Surface.Translation.Typed where

open import Data.Fin using (zero; suc)
open import Data.Maybe using (Is-just; just; to-witness)
open import Data.Vec using (_∷_; [])

open import Core.Syntax as C
open import Core.Syntax.Derived as C
open import Core.Syntax.Renaming as C
open import Core.Derivations as C
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; ε to εˢ)
open import Surface.Syntax.CtxSuffix
open import Surface.Derivations.Algorithmic as S

open import Surface.Translation.Untyped

mutual
  {-
  A witness of
  τ' <: τ
  gets translated to a function of type
  τ' ⇒ τ
  -}
  μ-<: : {τ τ' : SType ℓ}
       → Γˢ ⊢[ θ , E ] τ' <: τ
       → CExpr ℓ
  μ-<: (ST-Base positive _ _) with to-witness positive
  ... | MkPD <:-ε = <:-ε
  μ-<: (ST-Arr <:₁ <:₂ (enriched τ₁⇒τ₂'δ) (enriched (TWF-Arr τ₁'δ _)))
    {-
    We need to build a function of type (τ₁ ⇒ τ₂') ⇒ (τ₁' ⇒ τ₂)
    Thus, we do the following:
    λ (τ₁ ⇒ τ₂').
      λ τ₁'.
        μ(<:₂)
          (#1
            (μ(<:₁) (#0)))
    -}
    = let arg-ε = μ-<: <:₁  -- ⦂ τ₁' ⇒ τ₁
          res-ε = μ-<: <:₂  -- ⦂ τ₂' ⇒ τ₂
       in CLam
            (μ-τ τ₁⇒τ₂'δ)
            (CLam
              (weaken-ε (μ-τ τ₁'δ))
              (act-ε (ext suc) res-ε ·
                (CVar (suc zero) ·
                  (weaken-ε-k 2 arg-ε · CVar zero)))
            )

  μ-τ : {τ : SType ℓ}
      → Γˢ ⊢[ θ , E ] τ
      → CExpr ℓ
  μ-τ (TWF-TrueRef {b = b} Γok) = ⌊μ⌋-b b
  μ-τ (TWF-Base {b = b} {b' = b'} ε₁δ ε₂δ)
    = let b̂ = ⌊μ⌋-b b
       in Σ[ b̂ ] CLam b̂ (μ-ε ε₁δ ≡̂ μ-ε ε₂δ of ⌊μ⌋-b b')
  μ-τ (TWF-Conj δ₁ δ₂) = ⟨ μ-τ δ₁ × μ-τ δ₂ ⟩
  μ-τ (TWF-Arr τ₁δ τ₂δ) = CΠ (μ-τ τ₁δ) (μ-τ τ₂δ)
  μ-τ (TWF-ADT consδs) = CADT (μ-cons consδs)

  μ-ε : ∀ {ε : STerm ℓ} {τ}
      → Γˢ ⊢[ θ , E of κ ] ε ⦂ τ
      → CExpr ℓ
  μ-ε (T-Unit Γok) = [ Cunit ⦂ CUnit ∣ eq-refl CUnit Cunit of CLam CUnit ⌊μ⌋-Τ ]
  μ-ε (T-Var {ι = ι} _ _) = CVar ι
  μ-ε (T-Abs (TWF-Arr domδ _) εδ) = CLam (μ-τ domδ) (μ-ε εδ)
  μ-ε (T-App ε₁δ ε₂δ _ _) = μ-ε ε₁δ · μ-ε ε₂δ
  μ-ε (T-Case resδ εδ branches) = CCase (μ-ε εδ) (μ-branches branches)
  μ-ε (T-Con {ι = ι} _ εδ adtτ) = CCon ι (μ-ε εδ) (μ-cons' adtτ)
  μ-ε (T-Sub εδ _ <:) = μ-<: <: · μ-ε εδ

  μ-cons' : {cons : S.ADTCons nₐ ℓ}
          → Γˢ ⊢[ θ , E ] ⊍ cons
          → C.ADTCons nₐ ℓ
  μ-cons' (TWF-ADT consδs) = μ-cons consδs

  μ-cons : {cons : S.ADTCons nₐ ℓ}
         → All (Γˢ ⊢[ θ , E ]_) cons
         → C.ADTCons nₐ ℓ
  μ-cons [] = []
  μ-cons (τδ ∷ consδ) = μ-τ τδ ∷ μ-cons consδ

  μ-branches : {branches : S.CaseBranches nₐ ℓ}
             → {cons : S.ADTCons nₐ ℓ}
             → S.BranchesHaveType θ E Γˢ cons branches τˢ
             → C.CaseBranches nₐ ℓ
  μ-branches NoBranches = []
  μ-branches (OneMoreBranch εδ bs) = {- TODO placeholder proper proof -} Cunit ∷ μ-branches bs

μ-Γ : {Γˢ : S.Ctx ℓ}
    → Γˢ ok[ θ , E ]
    → C.Ctx ℓ
μ-Γ TCTX-Empty = ⊘
μ-Γ (TCTX-Bind Γok τδ) = μ-Γ Γok , μ-τ τδ
