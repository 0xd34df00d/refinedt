module Surface.Derivations.Algorithmic.Theorems.Thinning.Size where

open import Data.Fin using (zero; suc; raise; #_)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Data.Nat.Tactic.RingSolver
open import Data.Vec.Base using (lookup; _∷_)
open import Function
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; subst; sym; cong; cong₂)
open Eq.≡-Reasoning

open import Common.Helpers
open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Subcontext
open import Surface.Syntax.Membership
open import Surface.Syntax.Renaming as R
open import Surface.Syntax.Substitution as S
open import Surface.Syntax.Substitution.Distributivity
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Helpers
open import Surface.Derivations.Algorithmic.Theorems.Agreement.Γok
open import Surface.Derivations.Algorithmic.Theorems.Agreement.Γok.WF
open import Surface.Derivations.Algorithmic.Theorems.Thinning
open import Surface.Derivations.Algorithmic.Theorems.Thinning.Size.Helpers
open import Surface.Derivations.Algorithmic.Theorems.Uniqueness

mutual
  Γ⊢ε⦂τ-thinning↓-size : (Γ⊂Γ' : k by Γ ⊂' Γ')
                       → (Γ'ok : Γ' ok[ θ , φ ])
                       → (εδ : Γ ⊢[ θ , φ of κ ] ε ⦂ τ)
                       → (acc : Acc _<_ (size-t εδ))
                       → size-t (Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok εδ acc) + size-ok (Γ⊢ε⦂τ-⇒-Γok εδ) ≡ size-t εδ + size-ok Γ'ok
  Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok (T-Unit Γok) _ = cong (2 +_) (+-comm (size-ok Γ'ok) (size-ok Γok))
  Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok (T-Var Γok _) _ = cong suc (+-comm (size-ok Γ'ok) (size-ok Γok))
  Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok (T-Abs τ₁⇒τ₂δ εδ) (acc rec)
    with τ₁⇒τ₂δ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok τ₁⇒τ₂δ (rec _ (s≤s (₁≤₂ _ _)))
    with τ₁⇒τ₂δ'@(TWF-Arr τ₁δ' τ₂δ') ← Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok τ₁⇒τ₂δ (rec _ (s≤s (₁≤₂ _ _)))
    with εδ↓ ← Γ⊢ε⦂τ-thinning↓-size (append-both Γ⊂Γ') (TCTX-Bind Γ'ok τ₁δ') εδ (rec _ (s≤s (₂≤₂ _ _)))
    with εδ' ← Γ⊢ε⦂τ-thinning↓ (append-both Γ⊂Γ') (TCTX-Bind Γ'ok τ₁δ') εδ (rec _ (s≤s (₂≤₂ _ _)))
    with TCTX-Bind Γok τ₁δ ← Γ⊢ε⦂τ-⇒-Γok εδ
    with TWF-Arr τ₁δ₀ τ₂δ₀ ← τ₁⇒τ₂δ
    with acc-τ₁ ← rec _ (s≤s (≤-trans (≤-trans (₁≤₂ _ (size-twf τ₂δ₀)) (n≤1+n _)) (₁≤₂ _ (size-t εδ))))
    with τ₁δ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok τ₁δ₀ acc-τ₁
    rewrite ∥Γ,τ-ok∥≡∥τδ∥ (TCTX-Bind Γ'ok τ₁δ') τ₁δ'
          | ∥Γ,τ-ok∥≡∥τδ∥ (TCTX-Bind Γok τ₁δ) τ₁δ
          | unique-Γok (Γ⊢τ-⇒-Γok τ₁δ₀) Γok
          | unique-Γ⊢τ (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok τ₁δ₀ acc-τ₁) τ₁δ'
          | unique-Γ⊢τ τ₁δ₀ τ₁δ
          | lemma₀ τ₁δ τ₂δ₀ τ₁⇒τ₂δ
          | cong (_+ size-ok Γ'ok) (lemma₀ τ₁δ τ₂δ₀ τ₁⇒τ₂δ)
          = cong suc $
              begin
                size-twf τ₁⇒τ₂δ' ⊔ size-t εδ' + size-ok Γok
              ≡⟨ +-distribʳ-⊔ _ _ (size-t εδ') ⟩
                (size-twf τ₁⇒τ₂δ' + size-ok Γok) ⊔ (size-t εδ' + size-ok Γok)
              ≡⟨ cong₂ (_⊔_) τ₁⇒τ₂δ↓ (lemma₁ τ₁δ↓ εδ↓) ⟩
                (size-twf τ₁⇒τ₂δ + size-ok Γ'ok) ⊔ (size-t εδ + size-ok Γ'ok)
              ≡⟨ sym (+-distribʳ-⊔ _ _ (size-t εδ)) ⟩
                size-twf τ₁⇒τ₂δ ⊔ size-t εδ + size-ok Γ'ok
              ∎
  Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok (T-App εδ εδ₁ resτ-≡ resτδ) (acc rec) = {! !}
  Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok (T-Case resδ εδ branches-well-typed) (acc rec) = {! !}
  Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok (T-Con ≡-prf εδ adtτ) (acc rec) = {! !}
  Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok (T-Sub εδ τδ <:δ) (acc rec) = {! !}

  Γ⊢τ-thinning↓-size : (Γ⊂Γ' : k by Γ ⊂' Γ')
                     → (Γ'ok : Γ' ok[ θ , φ ])
                     → (τδ : Γ ⊢[ θ , φ ] τ)
                     → (acc : Acc _<_ (size-twf τδ))
                     → size-twf (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok τδ acc) + size-ok (Γ⊢τ-⇒-Γok τδ) ≡ size-twf τδ + size-ok Γ'ok
  Γ⊢τ-thinning↓-size = {! !}
