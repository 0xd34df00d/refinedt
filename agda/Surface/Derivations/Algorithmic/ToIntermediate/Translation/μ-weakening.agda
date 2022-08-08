{-# OPTIONS --allow-unsolved-metas #-}

module Surface.Derivations.Algorithmic.ToIntermediate.Translation.μ-weakening where

open import Data.Fin using (zero; suc; raise; #_)
open import Data.Nat.Base
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans; sym)

open import Common.Inequalities
open import Common.Helpers

open import Intermediate.Syntax as I renaming (Γ to Γⁱ; ε to εⁱ)
open import Intermediate.Syntax.Renaming as IR
--open import Intermediate.Syntax.Renaming.Distributivity as IR
open import Surface.Syntax as S renaming (Γ to Γˢ; Γ' to Γ'ˢ; τ to τˢ; τ' to τ'ˢ; ε to εˢ)
open import Surface.Syntax.CtxSuffix as S renaming (Δ to Δˢ)
open import Surface.Syntax.Subcontext as S
open import Surface.Syntax.Renaming as SR
open import Surface.Syntax.Substitution.Distributivity
open import Surface.Derivations.Algorithmic as S renaming (θ to θˢ)
open import Surface.Derivations.Algorithmic.Theorems.Thinning.Enriched
open import Surface.Derivations.Algorithmic.Theorems.Uniqueness

open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Subst
open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Typed

mutual
  μ-<:-thinning-commutes : {Γˢ : S.Ctx (k + ℓ)}
                         → (Γ⊂Γ' : k by Γˢ ⊂' Γ'ˢ)
                         → (Γ'ok : Γ'ˢ ok[ θˢ , E ])
                         → (δ : Γˢ ⊢[ θˢ , E ] τ'ˢ <: τˢ)
                         → μ-<: (<:-thinning Γ⊂Γ' Γ'ok δ) ≡ IR.act-ε (ext-k' k suc) (μ-<: δ)
  μ-<:-thinning-commutes = {! !}

  μ-τ-thinning-commutes : {Γˢ : S.Ctx (k + ℓ)}
                        → (Γ⊂Γ' : k by Γˢ ⊂' Γ'ˢ)
                        → (Γ'ok : Γ'ˢ ok[ θˢ , E ])
                        → (τδ : Γˢ ⊢[ θˢ , E ] τˢ)
                        → μ-τ (Γ⊢τ-thinning Γ⊂Γ' Γ'ok τδ) ≡ IR.act-τ (ext-k' k suc) (μ-τ τδ)
  μ-τ-thinning-commutes = {! !}

  μ-ε-thinning-commutes : {Γˢ : S.Ctx (k + ℓ)}
                        → (Γ⊂Γ' : k by Γˢ ⊂' Γ'ˢ)
                        → (Γ'ok : Γ'ˢ ok[ θˢ , E ])
                        → (εδ : Γˢ ⊢[ θˢ , E of κ ] εˢ ⦂ τˢ)
                        → μ-ε (Γ⊢ε⦂τ-thinning Γ⊂Γ' Γ'ok εδ) ≡ IR.act-ε (ext-k' k suc) (μ-ε εδ)
  μ-ε-thinning-commutes = {! !}

μ-τ-weakening-commutes : (Γok : Γˢ ok[ θˢ , E ])
                       → (τ'δ : Γˢ ⊢[ θˢ , E ] τ'ˢ)
                       → (τδ  : Γˢ ⊢[ θˢ , E ] τˢ)
                       → μ-τ (Γ⊢τ-weakening Γok τ'δ τδ) ≡ IR.weaken-τ (μ-τ τδ)
μ-τ-weakening-commutes Γok τ'δ = μ-τ-thinning-commutes ignore-head (TCTX-Bind Γok τ'δ)

μ-ε-weakening-commutes : (Γok : Γˢ ok[ θˢ , E ])
                       → (τ'δ : Γˢ ⊢[ θˢ , E ] τ'ˢ)
                       → (εδ : Γˢ ⊢[ θˢ , E of κ ] εˢ ⦂ τˢ)
                       → μ-ε (Γ⊢ε⦂τ-weakening Γok τ'δ εδ) ≡ IR.weaken-ε (μ-ε εδ)
μ-ε-weakening-commutes Γok τ'δ = μ-ε-thinning-commutes ignore-head (TCTX-Bind Γok τ'δ)
