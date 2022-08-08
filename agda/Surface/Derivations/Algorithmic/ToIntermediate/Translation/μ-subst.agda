{-# OPTIONS --allow-unsolved-metas #-}

module Surface.Derivations.Algorithmic.ToIntermediate.Translation.μ-subst where

open import Data.Fin.Base using (zero; suc; raise)
open import Data.Nat.Base using (zero; suc)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; subst; sym; trans; cong)
open Eq.≡-Reasoning

open import Common.Helpers
open import Data.Fin.Extra

open import Intermediate.Syntax as I renaming (Γ to Γⁱ; ε to εⁱ)
open import Intermediate.Syntax.Renaming as IR
open import Intermediate.Syntax.Substitution as IS
open import Surface.Syntax as S renaming (Γ to Γˢ; Γ' to Γ'ˢ; τ to τˢ; τ' to τ'ˢ; ε to εˢ)
open import Surface.Syntax.CtxSuffix as S renaming (Δ to Δˢ)
open import Surface.Syntax.Membership as S
open import Surface.Syntax.Renaming as SR
open import Surface.Syntax.Subcontext as S
open import Surface.Syntax.Substitution as SS
open import Surface.Syntax.Substitution.Distributivity
open import Surface.Derivations.Algorithmic as S renaming (θ to θˢ)
open import Surface.Derivations.Algorithmic.Theorems.Uniqueness

open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Aliases
open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Subst
open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Typed
open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.μ-weakening

μ-Var-sub-distr : (Δ : ,-CtxSuffix ℓ σˢ k)
                → (argδ : Γˢ ⊢[ θˢ , E of not-t-sub ] εˢ ⦂ σ'ˢ)
                -- → (<:δ : Γˢ ⊢[ θˢ , E ] σ'ˢ <: σˢ)
                → (codδ : Γˢ ,σ, Δ ⊢[ θˢ , E of not-t-sub ] SVar ι ⦂ τˢ)
                → (resδ : Γˢ ++ [↦Δ εˢ ] Δ  ⊢[ θˢ , E of not-t-sub ] [ ℓ ↦ε<ˢ εˢ ] SVar ι ⦂ [ ℓ ↦τ<ˢ εˢ ] τˢ)
                → μ-ε resδ ≡ [ ℓ ↦ε<ⁱ μ-ε argδ ] μ-ε codδ
μ-Var-sub-distr {k = k} Δ argδ (T-Var {ι = ι} Γok x) resδ
  with ctx-idx k <>? ι
     | resδ
... | less _ | T-Var _ _ = refl
... | greater _ | T-Var _ _ = refl
... | equal refl | resδ = {! !}

mutual
  μ-ε-sub-distr : (Δ : ,-CtxSuffix ℓ σˢ k)
                → (argδ : Γˢ ⊢[ θˢ , E of not-t-sub ] εˢ ⦂ σ'ˢ)
                → (codδ : Γˢ ,σ, Δ ⊢[ θˢ , E of κ ] ε'ˢ ⦂ τˢ)
                → (resδ : Γˢ ++ [↦Δ εˢ ] Δ  ⊢[ θˢ , E of κ ] [ ℓ ↦ε<ˢ εˢ ] ε'ˢ ⦂ [ ℓ ↦τ<ˢ εˢ ] τˢ)
                → μ-ε resδ ≡ [ ℓ ↦ε<ⁱ μ-ε argδ ] μ-ε codδ
  μ-ε-sub-distr Δ argδ (T-Unit _) (T-Unit _) = refl
  μ-ε-sub-distr Δ argδ (T-Var Γok ∈) resδ = μ-Var-sub-distr Δ argδ (T-Var Γok ∈) resδ
  μ-ε-sub-distr Δ argδ (T-Abs codδ) (T-Abs resδ) = {! !}
  μ-ε-sub-distr Δ argδ (T-App codδ codδ₁ resτ-≡) (T-App resδ resδ₁ resτ-≡₁) = {! !}
  μ-ε-sub-distr Δ argδ (T-Case resδ₁ codδ branches-well-typed) (T-Case resδ resδ₂ branches-well-typed₁) = {! !}
  μ-ε-sub-distr Δ argδ (T-Con ≡-prf codδ adtτ) (T-Con ≡-prf₁ resδ adtτ₁) = {! !}
  μ-ε-sub-distr Δ argδ (T-Sub codδ <:δ) (T-Sub resδ <:δ₁) = {! !}

  μ-τ-sub-distr : (Δ : ,-CtxSuffix ℓ σˢ k)
                → (argδ : Γˢ ⊢[ θˢ , E of not-t-sub ] εˢ ⦂ σ'ˢ)
                → (codδ : Γˢ ,σ, Δ ⊢[ θˢ , E ] τˢ)
                → (resδ : Γˢ ++ [↦Δ εˢ ] Δ ⊢[ θˢ , E ] [ ℓ ↦τ<ˢ εˢ ] τˢ)
                → μ-τ resδ ≡ [ ℓ ↦τ<ⁱ μ-ε argδ ] μ-τ codδ
  μ-τ-sub-distr = {! !}

μ-τ-sub-front-distr : {Γˢ : S.Ctx ℓ}
                    → (argδ : Γˢ ⊢[ θˢ , E of not-t-sub ] ε₂ˢ ⦂ τ₁ˢ)
                    → (codδ : Γˢ ,ˢ τ₁ˢ ⊢[ θˢ , E ] τ₂ˢ)
                    → (resδ : Γˢ ⊢[ θˢ , E ] [ zero ↦τˢ ε₂ˢ ] τ₂ˢ)
                    → μ-τ resδ ≡ [ zero ↦τⁱ μ-ε argδ ] μ-τ codδ
μ-τ-sub-front-distr {ε₂ˢ = ε₂ˢ} {τ₁ˢ = τ₁ˢ} {τ₂ˢ = τ₂ˢ} argδ codδ resδ
  = let SS-eq = sym (SS.first-↦τ< ε₂ˢ τ₂ˢ)
        resδ' : _ ⊢[ _ , E ] [ _ ↦τ<ˢ ε₂ˢ ] τ₂ˢ
        resδ' = subst (_ ⊢[ _ , E ]_) SS-eq resδ
     in begin
          μ-τ resδ
        ≡⟨ lemma SS-eq resδ resδ' ⟩
          μ-τ resδ'
        ≡⟨ μ-τ-sub-distr [ τ₁ˢ ] argδ codδ resδ' ⟩
          ([ _ ↦τ<ⁱ μ-ε argδ ] μ-τ codδ)
        ≡⟨ IS.first-↦τ< (μ-ε argδ) (μ-τ codδ) ⟩
          [ zero ↦τⁱ μ-ε argδ ] μ-τ codδ
        ∎
  where
  lemma : {τ₁ τ₂ : SType ℓ}
        → τ₁ ≡ τ₂
        → (δ₁ : Γˢ ⊢[ θˢ , E ] τ₁)
        → (δ₂ : Γˢ ⊢[ θˢ , E ] τ₂)
        → μ-τ δ₁ ≡ μ-τ δ₂
  lemma refl δ₁ δ₂ = cong μ-τ (unique-Γ⊢τ δ₁ δ₂)
