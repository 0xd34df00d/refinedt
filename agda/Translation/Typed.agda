{-# OPTIONS --safe #-}

module Translation.Typed where

open import Data.Fin using (zero; suc)
open import Data.Maybe using (Is-just; just; to-witness)
open import Data.Vec using (_∷_; [])

open import Core.Syntax as C
open import Core.Syntax.Derived as C
open import Core.Syntax.Renaming as C
open import Core.Derivations as C
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; ε to εˢ)
open import Surface.Syntax.CtxSuffix
open import Surface.Derivations as S renaming (_⊢_⦂_ to _⊢ˢ_⦂_)
open import Surface.Derivations.Enriched
open import Surface.Theorems.Agreement
open import Surface.Theorems.Subtyping

open import Translation.Untyped

mutual
  μ-<: : {τ τ' : SType ℓ}
       → Γˢ ⊢ₑ τ <: τ'
       → CExpr ℓ
  μ-<: (ST-Base oracle positive _ _) with to-witness positive
  ... | MkPD <:-ε = <:-ε
  μ-<: (ST-Arr <:₁ <:₂ δτ@(TWF-Arr δτ₁ δτ₂ _) (TWF-Arr δτ₁' δτ₂' _)) =
    {-
    We need to build a function of type (τ₁ ⇒ τ₂) ⇒ (τ₁' ⇒ τ₂')
    Thus, we do the following:
    λ (τ₁ ⇒ τ₂).
      λ τ₁'.
        μ(<:₂)
          (#1
            (μ(<:₁) (#0)))
    -}
    let arg-ε = μ-<: <:₁  -- ⦂ τ₁' ⇒ τ₁
        res-ε = μ-<: <:₂  -- ⦂ τ₂ ⇒ τ₂'
     in CLam
          (μ-τ δτ)
          (CLam
            (weaken-ε (μ-τ δτ₁'))
            (act-ε (ext suc) res-ε ·
              (CVar (suc zero) ·
                (weaken-ε-k 2 arg-ε · CVar zero)))
          )

  μ-τ : {τ : SType ℓ}
      → Γˢ ⊢ₑ τ
      → CExpr ℓ
  μ-τ (TWF-TrueRef {b = b} Γok) = ⌊μ⌋-b b
  μ-τ (TWF-Base {b = b} δε₁ δε₂ _ _) = Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) (μ-ε δε₁ ≡̂ μ-ε δε₂ of ⌊μ⌋-b b)
  μ-τ (TWF-Conj δ₁ δ₂ _) = ⟨ μ-τ δ₁ × μ-τ δ₂ ⟩
  μ-τ (TWF-Arr δτ₁ δτ₂ _) = CΠ (μ-τ δτ₁) (μ-τ δτ₂)
  μ-τ (TWF-ADT consδs _) = CADT (μ-cons consδs)

  μ-ε : ∀ {ε : STerm ℓ} {τ}
      → Γˢ ⊢ₑ ε ⦂ τ
      → CExpr ℓ
  μ-ε (T-Unit Γok _) = [ Cunit ⦂ CUnit ∣ eq-refl CUnit Cunit of CLam CUnit ⌊μ⌋-Τ ]
  μ-ε (T-Var {ι = ι} _ _ _) = CVar ι
  μ-ε (T-Abs δarr δε _ _) = CLam (μ-τ δarr) (μ-ε δε)
  μ-ε (T-App δε₁ δε₂ _ _ _) = μ-ε δε₁ · μ-ε δε₂
  μ-ε (T-Case resδ δε branches _) = CCase (μ-ε δε) (μ-branches branches)
  μ-ε (T-Con {ι = ι} _ δε (TWF-ADT consδs _) _) = CCon ι (μ-ε δε) (μ-cons consδs)
  μ-ε (T-Sub δε τ'δ <: _) = μ-<: <: · μ-ε δε
  μ-ε (T-RConv δε _ _ _) = μ-ε δε

  μ-cons : {cons : S.ADTCons nₐ ℓ}
         → All (Γˢ ⊢ₑ_) cons
         → C.ADTCons nₐ ℓ
  μ-cons [] = []
  μ-cons (τ ∷ cons) = μ-τ τ ∷ μ-cons cons

  μ-branches : {branches : S.CaseBranches nₐ ℓ}
             → {cons : S.ADTCons nₐ ℓ}
             → BranchesHaveTypeₑ Γˢ cons branches τˢ
             → C.CaseBranches nₐ ℓ
  μ-branches NoBranches = []
  μ-branches (OneMoreBranch εδ bs) = {- TODO -} Cunit ∷ μ-branches bs
