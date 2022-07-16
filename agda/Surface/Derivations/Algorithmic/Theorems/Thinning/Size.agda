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
  <:-thinning↓-size : (Γ⊂Γ' : k by Γ ⊂' Γ')
                    → (Γ'ok : Γ' ok[ θ , E ])
                    → (<:δ : Γ ⊢[ θ , E ] τ' <: τ)
                    → (acc : Acc _<_ (size-<: <:δ))
                    → size-<: (<:-thinning↓ Γ⊂Γ' Γ'ok <:δ acc) + size-ok (Γ⊢τ'<:τ-⇒-Γok <:δ)
                      ≡
                      size-<: <:δ + size-ok Γ'ok
  <:-thinning↓-size Γ⊂Γ' Γ'ok (ST-Base is-just (enriched ρ₁δ) (enriched ρ₂δ)) (acc rec)
    with Γok ← Γ⊢τ-⇒-Γok ρ₁δ
       | ρ₁δ' ← Γ⊢τ-thinning↓       Γ⊂Γ' Γ'ok ρ₁δ (rec _ (s≤s (₁≤₂ _ _)))
       | ρ₁δ↓ ← Γ⊢τ-thinning↓-size  Γ⊂Γ' Γ'ok ρ₁δ (rec _ (s≤s (₁≤₂ _ _)))
       | ρ₂δ' ← Γ⊢τ-thinning↓       Γ⊂Γ' Γ'ok ρ₂δ (rec _ (s≤s (₂≤₂ _ _)))
       | ρ₂δ↓ ← Γ⊢τ-thinning↓-size  Γ⊂Γ' Γ'ok ρ₂δ (rec _ (s≤s (₂≤₂ _ _)))
    rewrite unique-Γok (Γ⊢τ-⇒-Γok ρ₂δ) Γok
          = cong suc (⊔-+-pairwise-≡ (size-ok Γok) (size-ok Γ'ok) ρ₁δ↓ ρ₂δ↓)
  <:-thinning↓-size Γ⊂Γ' Γ'ok <:δ@(ST-Arr <:₁δ <:₂δ (enriched τ₁⇒τ₂'δ) (enriched τ₁'⇒τ₂δ)) (acc rec)
    with Γok ← Γ⊢τ-⇒-Γok τ₁⇒τ₂'δ
       | τ₁⇒τ₂'δ' ← Γ⊢τ-thinning↓      Γ⊂Γ' Γ'ok τ₁'⇒τ₂δ (rec _ (<₄ (ST-Arr-size-vec <:δ) (# 3)))
       | τ₁⇒τ₂'δ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok τ₁'⇒τ₂δ (rec _ (<₄ (ST-Arr-size-vec <:δ) (# 3)))
       | τ₁'⇒τ₂δ' ← Γ⊢τ-thinning↓      Γ⊂Γ' Γ'ok τ₁⇒τ₂'δ (rec _ (<₄ (ST-Arr-size-vec <:δ) (# 2)))
       | τ₁'⇒τ₂δ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok τ₁⇒τ₂'δ (rec _ (<₄ (ST-Arr-size-vec <:δ) (# 2)))
       | <:₁δ' ← <:-thinning↓      Γ⊂Γ' Γ'ok <:₁δ (rec _ (<₄ (ST-Arr-size-vec <:δ) (# 0)))
       | <:₁δ↓ ← <:-thinning↓-size Γ⊂Γ' Γ'ok <:₁δ (rec _ (<₄ (ST-Arr-size-vec <:δ) (# 0)))
    with TWF-Arr τ₁δ' τ₂'δ' ← τ₁⇒τ₂'δ'
    with <:₂δ' ← <:-thinning↓      (append-both Γ⊂Γ') (TCTX-Bind Γ'ok τ₁δ') <:₂δ (rec _ (<₄ (ST-Arr-size-vec <:δ) (# 1)))
       | <:₂δ↓ ← <:-thinning↓-size (append-both Γ⊂Γ') (TCTX-Bind Γ'ok τ₁δ') <:₂δ (rec _ (<₄ (ST-Arr-size-vec <:δ) (# 1)))
       | <₁ ← <₄ (ST-Arr-size-vec <:δ) (# 3)
    with TWF-Arr τ₁'δ τ₂δ ← τ₁'⇒τ₂δ
    with τ₁δ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok τ₁'δ (rec _ (≤-trans (s≤s (<⇒≤ (s≤s (₁≤₂ _ _)))) <₁))
    rewrite unique-Γ⊢τ (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok τ₁'δ (rec _ (≤-trans (s≤s (<⇒≤ (s≤s (₁≤₂ _ _)))) <₁))) τ₁δ'
          | unique-Γok (Γ⊢τ-⇒-Γok τ₁'δ) Γok
          | unique-Γok (Γ⊢τ'<:τ-⇒-Γok <:₁δ) Γok
          | lemma₀ τ₁δ' τ₂'δ' τ₁⇒τ₂'δ'
          | cong (_+ size-ok Γok) (lemma₀ τ₁δ' τ₂'δ' τ₁⇒τ₂'δ')
          | lemma₀ τ₁'δ τ₂δ τ₁'⇒τ₂δ
          | cong (_+ size-ok Γ'ok) (lemma₀ τ₁'δ τ₂δ τ₁'⇒τ₂δ)
          | ∥Γ,τ-ok∥≡∥τδ∥ (Γ⊢τ'<:τ-⇒-Γok <:₂δ) τ₁'δ
          | ∥Γ,τ-ok∥≡∥τδ∥ (TCTX-Bind Γ'ok τ₁δ') τ₁δ'
          = cong suc (lemma₃ (size-ok Γok) (size-ok Γ'ok) <:₁δ↓ <:₂δ↓ τ₁δ↓ τ₁'⇒τ₂δ↓ τ₁⇒τ₂'δ↓)
  <:-thinning↓-size Γ⊂Γ' Γ'ok (ST-ADT (enriched ⊍δ)) (acc rec) = {! !}

  Γ⊢τ-thinning↓-size : (Γ⊂Γ' : k by Γ ⊂' Γ')
                     → (Γ'ok : Γ' ok[ θ , φ ])
                     → (τδ : Γ ⊢[ θ , φ ] τ)
                     → (acc : Acc _<_ (size-twf τδ))
                     → size-twf (Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok τδ acc) + size-ok (Γ⊢τ-⇒-Γok τδ)
                       ≡
                       size-twf τδ + size-ok Γ'ok
  Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok (TWF-TrueRef Γok) _ = cong suc (+-comm (size-ok Γ'ok) (size-ok Γok))
  Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok (TWF-Base ε₁δ ε₂δ) (acc rec)
    with Γ,Τ-ok@(TCTX-Bind Γok (TWF-TrueRef Γok')) ← Γ⊢ε⦂τ-⇒-Γok ε₁δ
       | ε₁δ' ← Γ⊢ε⦂τ-thinning↓      (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₁δ (rec _ (s≤s (₁≤₂ _ _)))
       | ε₂δ' ← Γ⊢ε⦂τ-thinning↓      (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₂δ (rec _ (s≤s (₂≤₂ _ _)))
       | ε₁δ↓ ← Γ⊢ε⦂τ-thinning↓-size (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₁δ (rec _ (s≤s (₁≤₂ _ _)))
       | ε₂δ↓ ← Γ⊢ε⦂τ-thinning↓-size (append-both Γ⊂Γ') (TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)) ε₂δ (rec _ (s≤s (₂≤₂ _ _)))
    rewrite unique-Γok (Γ⊢ε⦂τ-⇒-Γok ε₂δ) Γ,Τ-ok
          | unique-Γok Γok' Γok
          | m≤n⇒m⊔n≡n (n≤1+n (size-ok Γok))
          | m≤n⇒m⊔n≡n (n≤1+n (size-ok Γ'ok))
          = cong suc (⊔-+-pairwise-≡ (size-ok Γok) (size-ok Γ'ok) (un-suc (un-suc ε₁δ↓)) (un-suc (un-suc ε₂δ↓)))
  Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok (TWF-Conj τ₁δ τ₂δ) (acc rec)
    with Γok ← Γ⊢τ-⇒-Γok τ₁δ
       | τ₁δ' ← Γ⊢τ-thinning↓      Γ⊂Γ' Γ'ok τ₁δ (rec _ (s≤s (₁≤₂ _ _)))
       | τ₂δ' ← Γ⊢τ-thinning↓      Γ⊂Γ' Γ'ok τ₂δ (rec _ (s≤s (₂≤₂ _ _)))
       | τ₁δ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok τ₁δ (rec _ (s≤s (₁≤₂ _ _)))
       | τ₂δ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok τ₂δ (rec _ (s≤s (₂≤₂ _ _)))
    rewrite unique-Γok (Γ⊢τ-⇒-Γok τ₂δ) Γok
          = cong suc (⊔-+-pairwise-≡ (size-ok Γok) (size-ok Γ'ok) τ₁δ↓ τ₂δ↓)
  Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok (TWF-Arr τ₁δ τ₂δ) (acc rec)
    with Γok ← Γ⊢τ-⇒-Γok τ₁δ
       | τ₁δ' ← Γ⊢τ-thinning↓      Γ⊂Γ' Γ'ok τ₁δ (rec _ (s≤s (₁≤₂ _ _)))
       | τ₁δ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok τ₁δ (rec _ (s≤s (₁≤₂ _ _)))
    with Γ,τ₁-ok@(TCTX-Bind Γok' τ₁δ₀) ← Γ⊢τ-⇒-Γok τ₂δ
       | τ₂δ' ← Γ⊢τ-thinning↓      (append-both Γ⊂Γ') (TCTX-Bind Γ'ok τ₁δ') τ₂δ (rec _ (s≤s (₂≤₂ _ _)))
       | τ₂δ↓ ← Γ⊢τ-thinning↓-size (append-both Γ⊂Γ') (TCTX-Bind Γ'ok τ₁δ') τ₂δ (rec _ (s≤s (₂≤₂ _ _)))
    rewrite unique-Γ⊢τ τ₁δ₀ τ₁δ
          | unique-Γok Γok' Γok
          | m≤n⇒m⊔n≡n (<⇒≤ (∥Γok∥≤∥Γ⊢τ∥ Γok τ₁δ))
          | m≤n⇒m⊔n≡n (<⇒≤ (∥Γok∥≤∥Γ⊢τ∥ Γ'ok τ₁δ'))
          = let τ₂δ↓ = un-suc τ₂δ↓
             in cong suc (⊔-+-pairwise-≡ (size-ok Γok) (size-ok Γ'ok) τ₁δ↓ (lemma₁ {a' = size-twf τ₁δ'} τ₁δ↓ τ₂δ↓))
  Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok (TWF-ADT consδs@(τδ ∷ _)) (acc rec)
    with Γok ← Γ⊢τ-⇒-Γok τδ
    with consδs' ← cons-thinning↓      Γ⊂Γ'     Γ'ok consδs (rec _ ≤-refl)
       | consδs↓ ← cons-thinning↓-size Γ⊂Γ' Γok Γ'ok consδs (rec _ ≤-refl)
       = cong suc consδs↓

  cons-thinning↓-size : {cons : ADTCons (Mkℕₐ (suc n)) (k + ℓ)}
                      → (Γ⊂Γ' : k by Γ ⊂' Γ')
                      → (Γok : Γ ok[ θ , φ ])
                      → (Γ'ok : Γ' ok[ θ , φ ])
                      → (consδs : All (Γ ⊢[ θ , φ ]_) cons)
                      → (acc : Acc _<_ (size-all-cons consδs))
                      → size-all-cons (cons-thinning↓ Γ⊂Γ' Γ'ok consδs acc) + size-ok Γok
                        ≡
                        size-all-cons consδs + size-ok Γ'ok
  cons-thinning↓-size {n = zero} Γ⊂Γ' Γok Γ'ok (τδ ∷ []) (acc rec)
    with τδ' ← Γ⊢τ-thinning↓      Γ⊂Γ' Γ'ok τδ (rec _ (s≤s (₁≤₂ _ _)))
       | τδ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok τδ (rec _ (s≤s (₁≤₂ _ _)))
    rewrite unique-Γok (Γ⊢τ-⇒-Γok τδ) Γok
          | ⊔-identityʳ (size-twf τδ')
          | ⊔-identityʳ (size-twf τδ)
          = cong suc τδ↓
  cons-thinning↓-size {n = suc _} Γ⊂Γ' Γok Γ'ok (τδ ∷ consδs) (acc rec)
    with τδ' ← Γ⊢τ-thinning↓      Γ⊂Γ' Γ'ok τδ (rec _ (s≤s (₁≤₂ _ _)))
       | τδ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok τδ (rec _ (s≤s (₁≤₂ _ _)))
       | consδs' ← cons-thinning↓      Γ⊂Γ'     Γ'ok consδs (rec _ (s≤s (₂≤₂ _ _)))
       | consδs↓ ← cons-thinning↓-size Γ⊂Γ' Γok Γ'ok consδs (rec _ (s≤s (₂≤₂ _ _)))
    rewrite unique-Γok (Γ⊢τ-⇒-Γok τδ) Γok
          = cong suc (⊔-+-pairwise-≡ (size-ok Γok) (size-ok Γ'ok) τδ↓ consδs↓)

  Γ⊢ε⦂τ-thinning↓-size : (Γ⊂Γ' : k by Γ ⊂' Γ')
                       → (Γ'ok : Γ' ok[ θ , φ ])
                       → (εδ : Γ ⊢[ θ , φ of κ ] ε ⦂ τ)
                       → (acc : Acc _<_ (size-t εδ))
                       → size-t (Γ⊢ε⦂τ-thinning↓ Γ⊂Γ' Γ'ok εδ acc) + size-ok (Γ⊢ε⦂τ-⇒-Γok εδ)
                         ≡
                         size-t εδ + size-ok Γ'ok
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
          = cong suc (⊔-+-pairwise-≡ (size-ok Γok) (size-ok Γ'ok) τ₁⇒τ₂δ↓ (lemma₂ τ₁δ↓ εδ↓))
  Γ⊢ε⦂τ-thinning↓-size {k = k} Γ⊂Γ' Γ'ok (T-App {τ₂ = τ₂} {ε₂ = ε₂} ε₁δ ε₂δ refl resτδ) (acc rec)
    with resτδ' ← Γ⊢τ-thinning↓ Γ⊂Γ' Γ'ok resτδ (rec _ (s≤s (₃≤₃ (size-t ε₁δ) (size-t ε₂δ) _)))
       | Γok ← Γ⊢τ-⇒-Γok resτδ
       | resτδ↓ ← Γ⊢τ-thinning↓-size Γ⊂Γ' Γ'ok resτδ (rec _ (s≤s (₃≤₃ (size-t ε₁δ) (size-t ε₂δ) _)))
    rewrite ρ-subst-distr-τ-0 (ext-k' k suc) ε₂ τ₂
    with ε₁δ' ← Γ⊢ε⦂τ-thinning↓      Γ⊂Γ' Γ'ok ε₁δ (rec _ (s≤s (₁≤₂ _ _)))
       | ε₂δ' ← Γ⊢ε⦂τ-thinning↓      Γ⊂Γ' Γ'ok ε₂δ (rec _ (s≤s (₂≤₃ (size-t ε₁δ) _ _)))
       | ε₁δ↓ ← Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok ε₁δ (rec _ (s≤s (₁≤₂ _ _)))
       | ε₂δ↓ ← Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok ε₂δ (rec _ (s≤s (₂≤₃ (size-t ε₁δ) _ _)))
    rewrite unique-Γok (Γ⊢ε⦂τ-⇒-Γok ε₁δ) Γok
          | unique-Γok (Γ⊢ε⦂τ-⇒-Γok ε₂δ) Γok
          = cong suc $
              begin
                size-t ε₁δ' ⊔ (size-t ε₂δ' ⊔ size-twf resτδ') + size-ok Γok
              ≡⟨ +-distribʳ-⊔³ (size-t ε₁δ') _ _ _ ⟩
                (size-t ε₁δ' + size-ok Γok) ⊔ (size-t ε₂δ' + size-ok Γok) ⊔ (size-twf resτδ' + size-ok Γok)
              ≡⟨ cong₃ (λ a b c → a ⊔ b ⊔ c) ε₁δ↓ ε₂δ↓ resτδ↓ ⟩
                (size-t ε₁δ + size-ok Γ'ok) ⊔ (size-t ε₂δ + size-ok Γ'ok) ⊔ (size-twf resτδ + size-ok Γ'ok)
              ≡⟨ sym (+-distribʳ-⊔³ (size-t ε₁δ) _ _ _) ⟩
                size-t ε₁δ ⊔ (size-t ε₂δ ⊔ size-twf resτδ) + size-ok Γ'ok
              ∎
  Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok (T-Case resδ εδ branches-well-typed) (acc rec) = {! !}
  Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok (T-Con ≡-prf εδ adtτ) (acc rec) = {! !}
  Γ⊢ε⦂τ-thinning↓-size Γ⊂Γ' Γ'ok (T-Sub εδ τδ <:δ) (acc rec) = {! !}
