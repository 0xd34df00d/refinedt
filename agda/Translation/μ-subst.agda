{-# OPTIONS --allow-unsolved-metas #-}

module Translation.μ-subst where

open import Data.Fin.Base using (zero; suc; raise)
open import Data.Nat.Base using (zero; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; subst; sym; trans; cong)
open Eq.≡-Reasoning

open import Common.Helpers
open import Data.Fin.Extra

open import Core.Syntax as C renaming (Γ to Γᶜ; ε to εᶜ; τ to τᶜ)
open import Core.Syntax.Derived as C
open import Core.Syntax.Renaming as CR
open import Core.Syntax.Substitution as CS
open import Core.Syntax.Derived.Substitution as CS
open import Core.Derivations as C renaming (_⊢_⦂_ to _⊢ᶜ_⦂_)
open import Intermediate.Syntax as I renaming (Γ to Γⁱ;
                                          τ to τⁱ; τ' to τ'ⁱ; τ₁ to τ₁ⁱ; τ₁' to τ₁'ⁱ; τ₂ to τ₂ⁱ; σ to σⁱ;
                                          ε to εⁱ; ε' to ε'ⁱ; ε₁ to ε₁ⁱ; ε₂ to ε₂ⁱ)
open import Intermediate.Syntax.CtxSuffix as I
open import Intermediate.Syntax.Renaming as IR
open import Intermediate.Syntax.Substitution as IS
open import Intermediate.Derivations.Algorithmic as I
open import Intermediate.Derivations.Algorithmic.Theorems.Agreement
open import Intermediate.Derivations.Algorithmic.Theorems.Thinning
open import Intermediate.Derivations.Algorithmic.Theorems.Uniqueness
--open import Intermediate.Theorems.Substitution as I

open import Translation.SubstUnique
open import Translation.Typed
open import Translation.Untyped
open import Translation.μ-weakening

⌊μ⌋-b-sub-id : ∀ k ε b
             → ⌊μ⌋-b {ℓ = k + ℓ} b ≡ [ ℓ ↦' ε ] (⌊μ⌋-b b)
⌊μ⌋-b-sub-id _ _ BUnit = refl

μ-ε-cong-unique : (εδ₁ : [ θ ] Γⁱ ⊢ εⁱ ⦂ τ₁ⁱ)
                → (εδ₂ : [ θ ] Γⁱ ⊢ εⁱ ⦂ τ₂ⁱ)
                → μ-ε εδ₁ ≡ μ-ε εδ₂
μ-ε-cong-unique εδ₁ εδ₂ with refl ← typing-uniqueness εδ₁ εδ₂ = cong μ-ε (unique-Γ⊢ε⦂τ εδ₁ εδ₂)

μ-Var-sub-distributes : (Δ : ,-CtxSuffix ℓ σⁱ k)
                      → (argδ : [ θ ] Γⁱ ⊢ εⁱ ⦂ σⁱ)
                      → (codδ : [ θ ] Γⁱ ,σ, Δ ⊢ SVar ι ⦂ τⁱ)
                      → (resδ : [ θ ] Γⁱ ++ [↦Δ εⁱ ] Δ ⊢ [ ℓ ↦ε< εⁱ ] SVar ι ⦂ [ ℓ ↦τ< εⁱ ] τⁱ)
                      → μ-ε resδ ≡ [ ℓ ↦' μ-ε argδ ] μ-ε codδ
μ-Var-sub-distributes {k = k} {εⁱ = εⁱ} Δ argδ (T-Var {ι = ι} Γok ∈) resδ with ctx-idx k <>? ι | resδ
... | less _ | T-Var _ _ = refl
... | greater _ | T-Var _ _ = refl
... | equal refl | resδ = trans
                            (μ-ε-cong-unique resδ (Γ⊢ε⦂τ-weakening-suffix (Γ⊢ε⦂τ-⇒-Γok resδ) argδ))
                            (μ-ε-weakening-suffix-commutes _ argδ)

mutual
  μ-ε-sub-distributes : (Δ : ,-CtxSuffix ℓ σⁱ k)
                      → (argδ : [ θ ] Γⁱ ⊢ εⁱ ⦂ σⁱ)
                      → (codδ : [ θ ] Γⁱ ,σ, Δ ⊢ ε'ⁱ ⦂ τⁱ)
                      → (resδ : [ θ ] Γⁱ ++ [↦Δ εⁱ ] Δ ⊢ [ ℓ ↦ε< εⁱ ] ε'ⁱ ⦂ [ ℓ ↦τ< εⁱ ] τⁱ)
                      → μ-ε resδ ≡ [ ℓ ↦' μ-ε argδ ] μ-ε codδ
  μ-ε-sub-distributes Δ argδ (T-Unit _) (T-Unit _) = refl
  μ-ε-sub-distributes Δ argδ codδ@(T-Var _ _) resδ = μ-Var-sub-distributes Δ argδ codδ resδ
  μ-ε-sub-distributes Δ argδ (T-Abs dom-arrδ dom-argδ) (T-Abs cod-arrδ cod-argδ) = {! !}
  μ-ε-sub-distributes Δ argδ (T-App domδ domδ₁ resτ-≡ resτδ) codδ = {! !}
  μ-ε-sub-distributes Δ argδ (T-Case resδ domδ branches-well-typed) codδ = {! !}
  μ-ε-sub-distributes Δ argδ (T-Con ≡-prf domδ adtτ) codδ = {! !}
  μ-ε-sub-distributes Δ argδ (T-SubW <: εδ) codδ = {! !}

  μ-τ-sub-distributes : (Δ : ,-CtxSuffix ℓ σⁱ k)
                      → (argδ : [ θ ] Γⁱ ⊢ εⁱ ⦂ σⁱ)
                      → (codδ : [ θ ] Γⁱ ,σ, Δ ⊢ τⁱ)
                      → (resδ : [ θ ] Γⁱ ++ [↦Δ εⁱ ] Δ ⊢ [ ℓ ↦τ< εⁱ ] τⁱ)
                      → μ-τ resδ ≡ [ ℓ ↦' μ-ε argδ ] μ-τ codδ
  μ-τ-sub-distributes {k = k} Δ argδ (TWF-TrueRef Γok) (TWF-TrueRef Γok₂) = ⌊μ⌋-b-sub-id k _ _
  μ-τ-sub-distributes {ℓ = ℓ} {k = k} {εⁱ = εⁱ} Δ argδ (TWF-Base {b = b} {ε₁ = ε₁} {b' = b'} {ε₂ = ε₂} ε₁δ₁ ε₂δ₁) (TWF-Base ε₁δ₂ ε₂δ₂)
    = begin

        Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) (μ-ε ε₁δ₂ ≡̂ μ-ε ε₂δ₂ of ⌊μ⌋-b b')

      ≡⟨ cong (Σ[ ⌊μ⌋-b b ]_) CLam≡-distr ⟩

        Σ[ ⌊μ⌋-b b ] ([ ℓ ↦' μ-ε argδ ] CLam (⌊μ⌋-b b) (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b'))

      ≡⟨ cong (Σ[_] ([ ℓ ↦' μ-ε argδ ] CLam (⌊μ⌋-b b) (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b')))
              (⌊μ⌋-b-sub-id k _ b) ⟩

        Σ[ [ ℓ ↦' μ-ε argδ ] ⌊μ⌋-b b ] ([ ℓ ↦' μ-ε argδ ] CLam (⌊μ⌋-b b) (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b'))

      ≡˘⟨ Σ-↦'-distr ℓ _ (⌊μ⌋-b b) (CLam (⌊μ⌋-b b) (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b')) ⟩

        [ ℓ ↦' μ-ε argδ ] Σ[ ⌊μ⌋-b b ] (CLam (⌊μ⌋-b b) (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b'))

      ∎
    where
    ε₁δ-distributes : μ-ε ε₁δ₂ ≡ [ ℓ ↦' μ-ε argδ ] μ-ε ε₁δ₁
    ε₁δ-distributes
      rewrite IS.act-ε-extensionality (IS.ext-replace-comm (IR.weaken-ε-k k εⁱ) (ctx-idx k)) ε₁
            | IR.act-ε-distr (raise k) suc εⁱ
            = μ-ε-sub-distributes (Δ , _) argδ ε₁δ₁ ε₁δ₂

    ε₂δ-distributes : μ-ε ε₂δ₂ ≡ [ ℓ ↦' μ-ε argδ ] μ-ε ε₂δ₁
    ε₂δ-distributes
      rewrite IS.act-ε-extensionality (IS.ext-replace-comm (IR.weaken-ε-k k εⁱ) (ctx-idx k)) ε₂
            | IR.act-ε-distr (raise k) suc εⁱ
            = μ-ε-sub-distributes (Δ , _) argδ ε₂δ₁ ε₂δ₂

    CLam≡-distr : CLam (⌊μ⌋-b b) (μ-ε ε₁δ₂ ≡̂ μ-ε ε₂δ₂ of ⌊μ⌋-b b')
                  ≡
                  [ ℓ ↦' μ-ε argδ ] CLam (⌊μ⌋-b b) (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b')
    CLam≡-distr
      = begin

          CLam (⌊μ⌋-b b) (μ-ε ε₁δ₂ ≡̂ μ-ε ε₂δ₂ of ⌊μ⌋-b b')

        ≡⟨ cong (CLam _) (≡̂-subst ε₁δ-distributes ε₂δ-distributes (⌊μ⌋-b-sub-id (suc k) _ _)) ⟩

          CLam (⌊μ⌋-b b) (([ ℓ ↦' μ-ε argδ ] μ-ε ε₁δ₁) ≡̂ ([ ℓ ↦' μ-ε argδ ] μ-ε ε₂δ₁) of ([ ℓ ↦' μ-ε argδ ] ⌊μ⌋-b b'))

        ≡˘⟨ cong (CLam _) (≡̂-↦'-distr ℓ (μ-ε argδ) (μ-ε ε₁δ₁) (μ-ε ε₂δ₁) (⌊μ⌋-b b')) ⟩

          CLam (⌊μ⌋-b b) ([ ℓ ↦' μ-ε argδ ] (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b'))

        ≡⟨ cong (λ τ → CLam τ ([ ℓ ↦' μ-ε argδ ] (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b'))) (⌊μ⌋-b-sub-id k _ _) ⟩

          CLam ([ ℓ ↦' μ-ε argδ ] ⌊μ⌋-b b) ([ ℓ ↦' μ-ε argδ ] (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b'))

        ≡˘⟨ CLam-↦'-distr ℓ _ (⌊μ⌋-b b) (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b') ⟩

          [ ℓ ↦' μ-ε argδ ] CLam (⌊μ⌋-b b) (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b')

        ∎
  μ-τ-sub-distributes {ℓ = ℓ} {k = k} Δ argδ (TWF-Conj ρ₁δ₁ ρ₂δ₁) (TWF-Conj ρ₁δ₂ ρ₂δ₂)
    = trans
        rec-distributes
        (sym (×-↦'-distr _ (μ-ε argδ) (μ-τ ρ₁δ₁) (μ-τ ρ₂δ₁)))
    where
    rec-distributes : ⟨ μ-τ ρ₁δ₂ × μ-τ ρ₂δ₂ ⟩ ≡ ⟨ ([ ℓ ↦' μ-ε argδ ] μ-τ ρ₁δ₁) × ([ ℓ ↦' μ-ε argδ ] μ-τ ρ₂δ₁) ⟩
    rec-distributes
      rewrite μ-τ-sub-distributes Δ argδ ρ₁δ₁ ρ₁δ₂
            | μ-τ-sub-distributes Δ argδ ρ₂δ₁ ρ₂δ₂
            = refl
  μ-τ-sub-distributes {ℓ = ℓ} {k = k} {εⁱ = εⁱ} Δ argδ (TWF-Arr {τ₂ = τ₂} argδ₁ resδ₁) (TWF-Arr argδ₂ resδ₂)
    = begin
        CΠ (μ-τ argδ₂) (μ-τ resδ₂)
      ≡⟨ cong (λ argδ → CΠ argδ (μ-τ resδ₂)) (μ-τ-sub-distributes Δ argδ argδ₁ argδ₂) ⟩
        CΠ ([ ℓ ↦' μ-ε argδ ] μ-τ argδ₁) (μ-τ resδ₂)
      ≡⟨ cong (CΠ _) resδ-subst-massage ⟩
        CΠ ([ ℓ ↦' μ-ε argδ ] μ-τ argδ₁) ([ ℓ ↦' μ-ε argδ ] μ-τ resδ₁)
      ≡˘⟨ CS.CΠ-↦'-distr ℓ _ (μ-τ argδ₁) (μ-τ resδ₁) ⟩
        ([ ℓ ↦' μ-ε argδ ] CΠ (μ-τ argδ₁) (μ-τ resδ₁))
      ∎
    where
    resδ-subst-massage : μ-τ resδ₂ ≡ [ ℓ ↦' μ-ε argδ ] μ-τ resδ₁
    resδ-subst-massage
      rewrite IS.act-τ-extensionality (IS.ext-replace-comm (IR.weaken-ε-k k εⁱ) (ctx-idx k)) τ₂
            | IR.act-ε-distr (raise k) suc εⁱ
            = μ-τ-sub-distributes (Δ , _) argδ resδ₁ resδ₂
  μ-τ-sub-distributes Δ argδ (TWF-ADT consδs₁) (TWF-ADT consδs₂) = {! !}

μ-τ-sub-front-distributes : {Γⁱ : I.Ctx ℓ}
                          → (argδ : [ θ ] Γⁱ ⊢ ε₂ⁱ ⦂ τ₁ⁱ)
                          → (codδ : [ θ ] Γⁱ , τ₁ⁱ ⊢ τ₂ⁱ)
                          → (resτδ : [ θ ] Γⁱ ⊢ [ zero ↦τ ε₂ⁱ ] τ₂ⁱ)
                          → μ-τ resτδ ≡ [ zero ↦  μ-ε argδ ] μ-τ codδ
μ-τ-sub-front-distributes {ε₂ⁱ = ε₂ⁱ} {τ₂ⁱ = τ₂ⁱ} argδ codδ resτδ
  = let act-ε-refl = sym (IR.act-ε-id (λ _ → refl) ε₂ⁱ)
        resτδ' = subst (λ ε → [ _ ] _ ⊢ [ zero ↦τ ε ] τ₂ⁱ) act-ε-refl resτδ
     in trans (helper (cong ([ zero ↦τ_] τ₂ⁱ) act-ε-refl) resτδ resτδ') (μ-τ-sub-distributes [ _ ] argδ codδ resτδ')
  where
  helper : {τ₁ τ₂ : SType ℓ}
         → τ₁ ≡ τ₂
         → (Γ⊢τ₁ : [ θ ] Γⁱ ⊢ τ₁)
         → (Γ⊢τ₂ : [ θ ] Γⁱ ⊢ τ₂)
         → μ-τ Γ⊢τ₁ ≡ μ-τ Γ⊢τ₂
  helper refl Γ⊢τ₁ Γ⊢τ₂ = cong μ-τ (unique-Γ⊢τ Γ⊢τ₁ Γ⊢τ₂)
