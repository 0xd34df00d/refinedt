{-# OPTIONS --safe #-}

module Surface.Theorems.Agreement.TypeWellFormedness where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (refl)

open import Surface.Syntax
open import Surface.Syntax.Membership
open import Surface.Derivations
open import Surface.Theorems.Helpers
open import Surface.Theorems.Thinning
open import Surface.Theorems.Substitution

τ∈Γ-⇒-Γ⊢τ : Γ ok
          → τ ∈ Γ at ι
          → Γ ⊢ τ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind Γok τδ) (∈-zero refl) = twf-weakening Γok τδ τδ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind Γok τδ) (∈-suc refl ∈) = twf-weakening Γok τδ (τ∈Γ-⇒-Γ⊢τ Γok ∈)

-- Referred to as T-implies-TWF in the paper
Γ⊢ε⦂τ-⇒-Γ⊢τ : Γ ⊢ ε ⦂ τ
            → Γ ⊢ τ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Unit Γok) = TWF-TrueRef Γok
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Var Γok ∈-prf) = τ∈Γ-⇒-Γ⊢τ Γok ∈-prf
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Abs arrδ _) = arrδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-App δ₁ δ₂) = sub-Γ⊢τ-front δ₂ (arr-wf-⇒-cod-wf (Γ⊢ε⦂τ-⇒-Γ⊢τ δ₁))
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Case resδ _ _) = resδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Con _ _ adtτ) = adtτ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Sub _ superδ _) = superδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-RConv _ τ'δ _) = τ'δ

{-
open import Surface.Theorems.Thinning.WF
open import Surface.Theorems.Agreement.TypeWellFormedness.WF

τ∈Γ-⇒-Γ⊢τ-smaller : (Γok : Γ ok)
                  → (∈ : τ ∈ Γ at ι)
                  → size-twf (τ∈Γ-⇒-Γ⊢τ Γok ∈) ≤ size-∈ Γok ∈
τ∈Γ-⇒-Γ⊢τ-smaller (TCTX-Bind Γok τδ) (∈-zero refl) = let r = twf-weakening-size Γok τδ τδ in {! !}
τ∈Γ-⇒-Γ⊢τ-smaller (TCTX-Bind Γok τδ) (∈-suc refl ∈) =
  let r₁ = twf-weakening-size Γok τδ (τ∈Γ-⇒-Γ⊢τ Γok ∈)
      r₂ = τ∈Γ-⇒-Γ⊢τ-smaller Γok ∈
   in {! !}

Γ⊢ε⦂τ-⇒-Γ⊢τ-smaller : (δ : Γ ⊢ ε ⦂ τ)
                    → size-twf (Γ⊢ε⦂τ-⇒-Γ⊢τ δ) < size-t δ
Γ⊢ε⦂τ-⇒-Γ⊢τ-smaller (T-Unit Γok) = s≤s ≤-refl
Γ⊢ε⦂τ-⇒-Γ⊢τ-smaller (T-Var Γok ∈-prf) = s≤s (≤-trans (τ∈Γ-⇒-Γ⊢τ-smaller Γok ∈-prf) (n≤m⊕n _ _))
Γ⊢ε⦂τ-⇒-Γ⊢τ-smaller (T-Abs _ _) = s≤s (m≤m⊕n _ _)
Γ⊢ε⦂τ-⇒-Γ⊢τ-smaller (T-App δ₁ δ₂) = let rec = Γ⊢ε⦂τ-⇒-Γ⊢τ-smaller δ₁ in {! !}
Γ⊢ε⦂τ-⇒-Γ⊢τ-smaller (T-Case resδ scrutτδ branches) = s≤s (n≤m⊕n⊕k (size-t scrutτδ) (size-twf resδ) (size-bs branches))
Γ⊢ε⦂τ-⇒-Γ⊢τ-smaller (T-Con _ _ _) = s≤s (n≤m⊕n _ _)
Γ⊢ε⦂τ-⇒-Γ⊢τ-smaller (T-Sub δ τ'δ <:) = s≤s (n≤m⊕n⊕k (size-t δ) (size-twf τ'δ) (size-st <:))
Γ⊢ε⦂τ-⇒-Γ⊢τ-smaller (T-RConv _ _ _) = s≤s (n≤m⊕n _ _)
-}
