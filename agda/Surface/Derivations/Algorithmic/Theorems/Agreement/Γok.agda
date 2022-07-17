{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Agreement.Γok where

open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Agreement.Γok.WF
open import Surface.Derivations.Algorithmic.Theorems.Helpers

Γok-tail-smaller : (δ : (Γ , τ) ok[ θ , φ ]) → size-ok (Γok-tail δ) < size-ok δ
Γok-tail-smaller (TCTX-Bind prevOk τδ) = s≤s (₁≤₂ (size-ok prevOk) (size-twf τδ))

-- Referred to as T-implies-TCTX in the paper
mutual
  Γ⊢ε⦂τ-⇒-Γok : Γ ⊢[ θ , φ of κ ] ε ⦂ τ → Γ ok[ θ , φ ]
  Γ⊢ε⦂τ-⇒-Γok (T-Unit gok) = gok
  Γ⊢ε⦂τ-⇒-Γok (T-Var gok _) = gok
  Γ⊢ε⦂τ-⇒-Γok (T-Abs arrδ _) = Γ⊢τ-⇒-Γok arrδ
  Γ⊢ε⦂τ-⇒-Γok (T-App δ₁ _ _ _) = Γ⊢ε⦂τ-⇒-Γok δ₁
  Γ⊢ε⦂τ-⇒-Γok (T-Case _ scrut _) = Γ⊢ε⦂τ-⇒-Γok scrut
  Γ⊢ε⦂τ-⇒-Γok (T-Con _ conArg _) = Γ⊢ε⦂τ-⇒-Γok conArg
  Γ⊢ε⦂τ-⇒-Γok (T-Sub δ _ _) = Γ⊢ε⦂τ-⇒-Γok δ

  -- Referred to as TWF-implies-TCTX in the paper
  Γ⊢τ-⇒-Γok : Γ ⊢[ θ , φ ] τ → Γ ok[ θ , φ ]
  Γ⊢τ-⇒-Γok (TWF-TrueRef gok) = gok
  Γ⊢τ-⇒-Γok (TWF-Base ε₁δ _) = Γok-tail (Γ⊢ε⦂τ-⇒-Γok ε₁δ)
  Γ⊢τ-⇒-Γok (TWF-Conj ρ₁δ _) = Γ⊢τ-⇒-Γok ρ₁δ
  Γ⊢τ-⇒-Γok (TWF-Arr argδ _) = Γ⊢τ-⇒-Γok argδ
  Γ⊢τ-⇒-Γok (TWF-ADT (px ∷ _)) = Γ⊢τ-⇒-Γok px

Γ⊢τ'<:τ-⇒-Γok : (<:δ : Γ ⊢[ θ , E ] τ' <: τ)
              → Γ ok[ θ , E ]
Γ⊢τ'<:τ-⇒-Γok (ST-Base _ (enriched ρ₁δ) _) = Γ⊢τ-⇒-Γok ρ₁δ
Γ⊢τ'<:τ-⇒-Γok (ST-Arr _ _ (enriched τ₁⇒τ₂'δ) _) = Γ⊢τ-⇒-Γok τ₁⇒τ₂'δ
Γ⊢τ'<:τ-⇒-Γok (ST-ADT (enriched ⊍δ)) = Γ⊢τ-⇒-Γok ⊍δ

private
  a<b-⇒-a<b⊕c : {b c a : ℕ} → a < b → a < suc (b ⊕ c)
  a<b-⇒-a<b⊕c {b} {c} a<b = <-trans a<b (s≤s (₁≤₂ b c))

  a<c-⇒-a<b⊕c : {b c a : ℕ} → a < c → a < suc (b ⊕ c)
  a<c-⇒-a<b⊕c {b} {c} a<c = <-trans a<c (s≤s (₂≤₂ b c))

abstract
  mutual
    Γ⊢ε⦂τ-⇒-Γok-smaller : (δ : Γ ⊢[ θ , φ of κ ] ε ⦂ τ)
                        → size-ok (Γ⊢ε⦂τ-⇒-Γok δ) < size-t δ
    Γ⊢ε⦂τ-⇒-Γok-smaller (T-Unit _) = s≤s (≤-step ≤-refl)
    Γ⊢ε⦂τ-⇒-Γok-smaller (T-Var _ _) = s≤s ≤-refl
    Γ⊢ε⦂τ-⇒-Γok-smaller (T-Abs arrδ _) = a<b-⇒-a<b⊕c (Γ⊢τ-⇒-Γok-smaller arrδ)
    Γ⊢ε⦂τ-⇒-Γok-smaller (T-App δ₁ _ _ _) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-smaller δ₁)
    Γ⊢ε⦂τ-⇒-Γok-smaller (T-Case _ scrutδ _) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-smaller scrutδ)
    Γ⊢ε⦂τ-⇒-Γok-smaller (T-Con _ conArg _) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-smaller conArg)
    Γ⊢ε⦂τ-⇒-Γok-smaller (T-Sub δ _ _) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-smaller δ)

    Γ⊢ε⦂τ-⇒-Γok-tail-smaller : (δ : (Γ , τ') ⊢[ θ , φ of κ ] ε ⦂ τ)
                             → size-ok (Γok-tail (Γ⊢ε⦂τ-⇒-Γok δ)) < size-t δ
    Γ⊢ε⦂τ-⇒-Γok-tail-smaller δ = <-trans (Γok-tail-smaller (Γ⊢ε⦂τ-⇒-Γok δ)) (Γ⊢ε⦂τ-⇒-Γok-smaller δ)

    Γ⊢τ-⇒-Γok-smaller : (δ : Γ ⊢[ θ , φ ] τ)
                      → size-ok (Γ⊢τ-⇒-Γok δ) < size-twf δ
    Γ⊢τ-⇒-Γok-smaller (TWF-TrueRef _) = s≤s ≤-refl
    Γ⊢τ-⇒-Γok-smaller (TWF-Base ε₁δ _) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-tail-smaller ε₁δ)
    Γ⊢τ-⇒-Γok-smaller (TWF-Conj ρ₁δ _) = a<b-⇒-a<b⊕c (Γ⊢τ-⇒-Γok-smaller ρ₁δ)
    Γ⊢τ-⇒-Γok-smaller (TWF-Arr argδ _) = a<b-⇒-a<b⊕c (Γ⊢τ-⇒-Γok-smaller argδ)
    Γ⊢τ-⇒-Γok-smaller (TWF-ADT (px ∷ pxs)) = <-trans
                                               (a<b-⇒-a<b⊕c (Γ⊢τ-⇒-Γok-smaller px))
                                               (n<1+n (suc (size-twf px ⊔ size-all-cons pxs)))

-- Various properties useful elsewhere

open import Surface.Derivations.Algorithmic.Theorems.Uniqueness

∥Γ,τ-ok∥≡∥τδ∥ : (Γ,τ-ok : (Γ , τ) ok[ θ , φ ])
              → (τδ : Γ ⊢[ θ , φ ] τ)
              → size-ok Γ,τ-ok ≡ suc (size-twf τδ)
∥Γ,τ-ok∥≡∥τδ∥ (TCTX-Bind Γok τδ) τδ'
  with ∥Γok∥<∥τδ∥ ← Γ⊢τ-⇒-Γok-smaller τδ
  rewrite unique-Γ⊢τ τδ' τδ
        | unique-Γok (Γ⊢τ-⇒-Γok τδ) Γok
        | m≤n⇒m⊔n≡n (<⇒≤ ∥Γok∥<∥τδ∥)
        = refl

∥Γok∥≤∥Γ⊢τ∥ : (Γok : Γ ok[ θ , φ ])
            → (τδ : Γ ⊢[ θ , φ ] τ)
            → size-ok Γok < size-twf τδ
∥Γok∥≤∥Γ⊢τ∥ Γok τδ rewrite unique-Γok Γok (Γ⊢τ-⇒-Γok τδ) = Γ⊢τ-⇒-Γok-smaller τδ

∥Γ⊢τ₁∥≤∥Γ,τ₁⊢ε⦂τ₂∥ : (τδ : Γ ⊢[ θ , φ ] τ₁)
                   → (εδ : Γ , τ₁ ⊢[ θ , φ of κ ] ε ⦂ τ₂)
                   → size-twf τδ ≤ size-t εδ
∥Γ⊢τ₁∥≤∥Γ,τ₁⊢ε⦂τ₂∥ τδ εδ
  with TCTX-Bind _ τδ' ← Γ⊢ε⦂τ-⇒-Γok εδ
     | smaller ← Γ⊢ε⦂τ-⇒-Γok-smaller εδ
  rewrite unique-Γ⊢τ τδ τδ'
        = ≤-trans (≤-stepsˡ 2 (m≤n⊔m _ _)) smaller
