module Surface.Derivations.Algorithmic.Theorems.Substitution where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (suc; zero; fromℕ<; raise)
open import Data.Nat.Base using (suc; zero; _+_)
open import Data.Nat.Properties using (≤-stepsʳ; ≤-refl; m≢1+n+m; suc-injective)
open import Data.Product renaming (_,_ to _,'_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Common.Helpers
open import Data.Fin.Extra

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Membership
open import Surface.Syntax.Renaming as R
open import Surface.Syntax.Substitution as S
open import Surface.Syntax.Substitution using ([_↦τ_]_; [_↦ε_]_; [_↦c_]_)
open import Surface.Syntax.Substitution.Stable
open import Surface.Syntax.Substitution.Distributivity as S
open import Surface.Syntax.Substitution.Commutativity
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Thinning

module M {σ : SType ℓ} (εδ : Γ ⊢[ θ , φ of κ ] ε ⦂ σ) where mutual
  sub-Γok : (Δ : ,-CtxSuffix ℓ σ k)
          → (Γ ,σ, Δ) ok[ θ , φ ]
          → (Γ ++ [↦Δ ε ] Δ) ok[ θ , φ ]
  sub-Γok [ _ ] (TCTX-Bind Γ-ok _) = Γ-ok
  sub-Γok (Δ , τ) (TCTX-Bind Γ,σ,Δ-ok τδ) = TCTX-Bind (sub-Γok Δ Γ,σ,Δ-ok) (sub-Γ⊢τ Δ τδ)

  sub-Γ⊢τ : (Δ : ,-CtxSuffix ℓ σ k)
          → Γ ,σ, Δ ⊢[ θ , φ ] τ
          → Γ ++ [↦Δ ε ] Δ ⊢[ θ , φ ] [ ℓ ↦τ< ε ] τ
  sub-Γ⊢τ Δ (TWF-TrueRef Γok) = TWF-TrueRef (sub-Γok Δ Γok)
  sub-Γ⊢τ Δ (TWF-Base ε₁δ ε₂δ) = {! !}
  sub-Γ⊢τ Δ (TWF-Conj τ₁δ τ₂δ) = TWF-Conj (sub-Γ⊢τ Δ τ₁δ) (sub-Γ⊢τ Δ τ₂δ)
  sub-Γ⊢τ Δ (TWF-Arr τ₁δ τ₂δ) = TWF-Arr (sub-Γ⊢τ Δ τ₁δ) {! (sub-Γ⊢τ (Δ , _) τ₂δ) !}
  sub-Γ⊢τ Δ (TWF-ADT consδs) = {! !}
