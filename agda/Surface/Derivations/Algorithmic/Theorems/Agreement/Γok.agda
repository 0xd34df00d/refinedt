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

Γok-tail-smaller : (Γ,τ-ok : (Γ , τ) ok[ θ , φ ]) → size-ok (Γok-tail Γ,τ-ok) < size-ok Γ,τ-ok
Γok-tail-smaller (TCTX-Bind Γok τδ) = s≤s (₁≤₂ (size-ok Γok) (size-twf τδ))

-- Referred to as T-implies-TCTX in the paper
Γ⊢ε⦂τ-⇒-Γok : Γ ⊢[ θ , φ of κ ] ε ⦂ τ → Γ ok[ θ , φ ]
Γ⊢ε⦂τ-⇒-Γok (T-Unit Γok) = Γok
Γ⊢ε⦂τ-⇒-Γok (T-Var Γok _) = Γok
Γ⊢ε⦂τ-⇒-Γok (T-Abs εδ) with TCTX-Bind Γok _ ← Γ⊢ε⦂τ-⇒-Γok εδ = Γok
Γ⊢ε⦂τ-⇒-Γok (T-App ε₁δ _ _) = Γ⊢ε⦂τ-⇒-Γok ε₁δ
Γ⊢ε⦂τ-⇒-Γok (T-Case _ scrut _) = Γ⊢ε⦂τ-⇒-Γok scrut
Γ⊢ε⦂τ-⇒-Γok (T-Con _ conArg _) = Γ⊢ε⦂τ-⇒-Γok conArg
Γ⊢ε⦂τ-⇒-Γok (T-Sub εδ _) = Γ⊢ε⦂τ-⇒-Γok εδ

-- Referred to as TWF-implies-TCTX in the paper
Γ⊢τ-⇒-Γok : Γ ⊢[ θ , φ ] τ → Γ ok[ θ , φ ]
Γ⊢τ-⇒-Γok (TWF-TrueRef Γok) = Γok
Γ⊢τ-⇒-Γok (TWF-Base ε₁δ _) = Γok-tail (Γ⊢ε⦂τ-⇒-Γok ε₁δ)
Γ⊢τ-⇒-Γok (TWF-Conj ρ₁δ _) = Γ⊢τ-⇒-Γok ρ₁δ
Γ⊢τ-⇒-Γok (TWF-Arr argδ _) = Γ⊢τ-⇒-Γok argδ
Γ⊢τ-⇒-Γok (TWF-ADT (τδ ∷ _)) = Γ⊢τ-⇒-Γok τδ

private
  a<b-⇒-a<b⊕c : {b c a : ℕ} → a < b → a < suc (b ⊕ c)
  a<b-⇒-a<b⊕c {b} {c} a<b = <-trans a<b (s≤s (₁≤₂ b c))

  a<c-⇒-a<b⊕c : {b c a : ℕ} → a < c → a < suc (b ⊕ c)
  a<c-⇒-a<b⊕c {b} {c} a<c = <-trans a<c (s≤s (₂≤₂ b c))

Γ⊢ε⦂τ-⇒-Γok-smaller : (δ : Γ ⊢[ θ , φ of κ ] ε ⦂ τ)
                    → size-ok (Γ⊢ε⦂τ-⇒-Γok δ) < size-t δ
Γ⊢ε⦂τ-⇒-Γok-smaller (T-Unit _) = s≤s (≤-step ≤-refl)
Γ⊢ε⦂τ-⇒-Γok-smaller (T-Var _ _) = s≤s ≤-refl
Γ⊢ε⦂τ-⇒-Γok-smaller (T-Abs εδ)
  with εδ-smaller ← Γ⊢ε⦂τ-⇒-Γok-smaller εδ
  with TCTX-Bind _ _ ← Γ⊢ε⦂τ-⇒-Γok εδ
     = s≤s (≤-trans (≤-stepsˡ 2 (m≤m⊔n _ _)) εδ-smaller)
Γ⊢ε⦂τ-⇒-Γok-smaller (T-App ε₁δ _ _) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-smaller ε₁δ)
Γ⊢ε⦂τ-⇒-Γok-smaller (T-Case _ scrutδ _) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-smaller scrutδ)
Γ⊢ε⦂τ-⇒-Γok-smaller (T-Con _ conArg _) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-smaller conArg)
Γ⊢ε⦂τ-⇒-Γok-smaller (T-Sub εδ _) = s≤s (<⇒≤ (Γ⊢ε⦂τ-⇒-Γok-smaller εδ))

Γ⊢ε⦂τ-⇒-Γok-tail-smaller : (εδ : (Γ , τ') ⊢[ θ , φ of κ ] ε ⦂ τ)
                         → size-ok (Γok-tail (Γ⊢ε⦂τ-⇒-Γok εδ)) < size-t εδ
Γ⊢ε⦂τ-⇒-Γok-tail-smaller εδ = <-trans (Γok-tail-smaller (Γ⊢ε⦂τ-⇒-Γok εδ)) (Γ⊢ε⦂τ-⇒-Γok-smaller εδ)

Γ⊢τ-⇒-Γok-smaller : (τδ : Γ ⊢[ θ , φ ] τ)
                  → size-ok (Γ⊢τ-⇒-Γok τδ) < size-twf τδ
Γ⊢τ-⇒-Γok-smaller (TWF-TrueRef _) = s≤s ≤-refl
Γ⊢τ-⇒-Γok-smaller (TWF-Base ε₁δ _) = a<b-⇒-a<b⊕c (Γ⊢ε⦂τ-⇒-Γok-tail-smaller ε₁δ)
Γ⊢τ-⇒-Γok-smaller (TWF-Conj ρ₁δ _) = a<b-⇒-a<b⊕c (Γ⊢τ-⇒-Γok-smaller ρ₁δ)
Γ⊢τ-⇒-Γok-smaller (TWF-Arr argδ _) = a<b-⇒-a<b⊕c (Γ⊢τ-⇒-Γok-smaller argδ)
Γ⊢τ-⇒-Γok-smaller (TWF-ADT (τδ ∷ τδs)) = <-trans
                                           (a<b-⇒-a<b⊕c (Γ⊢τ-⇒-Γok-smaller τδ))
                                           (n<1+n (suc (size-twf τδ ⊔ size-all-cons τδs)))

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
