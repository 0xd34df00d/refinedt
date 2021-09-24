{-# OPTIONS --allow-unsolved-metas #-}

open import Surface.Derivations.Algorithmic using (UniquenessOfOracles)

module Translation.μ-subst(oracles-equal : UniquenessOfOracles) where

open import Data.Fin.Base using (zero; suc; raise)
open import Data.Nat.Base using (zero; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; subst; sym; trans; cong)
open Eq.≡-Reasoning

open import Core.Syntax as C renaming (Γ to Γᶜ; ε to εᶜ; τ to τᶜ)
open import Core.Syntax.Derived as C
open import Core.Syntax.Renaming as CR
open import Core.Syntax.Substitution as CS
open import Core.Syntax.Derived.Substitution as CS
open import Core.Derivations as C renaming (_⊢_⦂_ to _⊢ᶜ_⦂_)
open import Surface.Syntax as S renaming (Γ to Γˢ;
                                          τ to τˢ; τ' to τ'ˢ; τ₁ to τ₁ˢ; τ₁' to τ₁'ˢ; τ₂ to τ₂ˢ; σ to σˢ;
                                          ε to εˢ; ε' to ε'ˢ; ε₁ to ε₁ˢ; ε₂ to ε₂ˢ)
open import Surface.Syntax.CtxSuffix as S
open import Surface.Syntax.Renaming as SR
open import Surface.Syntax.Substitution as SS
open import Surface.Derivations.Algorithmic as S
open import Surface.Derivations.Algorithmic.Theorems.Uniqueness(oracles-equal)
open import Surface.Theorems.Substitution as S

open import Translation.Untyped
open import Translation.Typed
open import Translation.SubstUnique(oracles-equal)

⌊μ⌋-b-sub-id : ∀ k ε b
             → ⌊μ⌋-b {ℓ = k + ℓ} b ≡ [ ℓ ↦' ε ] (⌊μ⌋-b b)
⌊μ⌋-b-sub-id _ _ BUnit = refl

mutual
  μ-ε-sub-commutes : (Δ : ,-CtxSuffix ℓ σˢ k)
                   → (argδ : Γˢ ⊢[ E of κ ] εˢ ⦂ σˢ)
                   → (domδ : Γˢ ,σ, Δ ⊢[ E of κ₁ ] ε'ˢ ⦂ τˢ)
                   → (codδ : Γˢ ++ [↦Δ εˢ ] Δ ⊢[ E of κ₂ ] [ ℓ ↦ε< εˢ ] ε'ˢ ⦂ [ ℓ ↦τ< εˢ ] τˢ)
                   → μ-ε codδ ≡ [ ℓ ↦' μ-ε argδ ] μ-ε domδ

  μ-τ-sub-commutes : (Δ : ,-CtxSuffix ℓ σˢ k)
                   → (argδ : Γˢ ⊢[ E of κ ] εˢ ⦂ σˢ)
                   → (domδ : Γˢ ,σ, Δ ⊢[ E ] τˢ)
                   → (codδ : Γˢ ++ [↦Δ εˢ ] Δ ⊢[ E ] [ ℓ ↦τ< εˢ ] τˢ)
                   → μ-τ codδ ≡ [ ℓ ↦' μ-ε argδ ] μ-τ domδ
  μ-τ-sub-commutes {k = k} Δ argδ (TWF-TrueRef Γok) (TWF-TrueRef Γok₂) = ⌊μ⌋-b-sub-id k _ _
  μ-τ-sub-commutes {ℓ = ℓ} {k = k} {εˢ = εˢ} Δ argδ (TWF-Base {b = b} {ε₁ = ε₁} {b' = b'} {ε₂ = ε₂} ε₁δ₁ ε₂δ₁) (TWF-Base ε₁δ₂ ε₂δ₂)
    = begin
        Σ[ ⌊μ⌋-b b ] CLam (⌊μ⌋-b b) (μ-ε ε₁δ₂ ≡̂ μ-ε ε₂δ₂ of ⌊μ⌋-b b')
      ≡⟨ cong (Σ[ ⌊μ⌋-b b ]_) CLam≡-distr ⟩
        Σ[ ⌊μ⌋-b b ] ([ ℓ ↦' μ-ε argδ ] CLam (⌊μ⌋-b b) (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b'))
      ≡⟨ cong
            (Σ[_] ([ ℓ ↦' μ-ε argδ ] CLam (⌊μ⌋-b b) (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b')))
            (⌊μ⌋-b-sub-id k _ b) ⟩
        Σ[ [ ℓ ↦' μ-ε argδ ] ⌊μ⌋-b b ] ([ ℓ ↦' μ-ε argδ ] CLam (⌊μ⌋-b b) (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b'))
      ≡˘⟨ act-Σ-commutes (CS.replace-at (CS.ctx-idx k) (CR.weaken-ε-k _ (μ-ε argδ))) (⌊μ⌋-b b) (CLam (⌊μ⌋-b b) (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b')) ⟩
        [ ℓ ↦' μ-ε argδ ] Σ[ ⌊μ⌋-b b ] (CLam (⌊μ⌋-b b) (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b'))
      ∎
    where
    ε₁δ-commutes : μ-ε ε₁δ₂ ≡ [ ℓ ↦' μ-ε argδ ] μ-ε ε₁δ₁
    ε₁δ-commutes
      rewrite SS.act-ε-extensionality (SS.ext-replace-comm (SR.weaken-ε-k k εˢ) (SS.ctx-idx k)) ε₁
            | SR.act-ε-distr (raise k) suc εˢ
            = μ-ε-sub-commutes (Δ , _) argδ ε₁δ₁ ε₁δ₂

    ε₂δ-commutes : μ-ε ε₂δ₂ ≡ [ ℓ ↦' μ-ε argδ ] μ-ε ε₂δ₁
    ε₂δ-commutes
      rewrite SS.act-ε-extensionality (SS.ext-replace-comm (SR.weaken-ε-k k εˢ) (SS.ctx-idx k)) ε₂
            | SR.act-ε-distr (raise k) suc εˢ
            = μ-ε-sub-commutes (Δ , _) argδ ε₂δ₁ ε₂δ₂

    CLam≡-distr : CLam (⌊μ⌋-b b) (μ-ε ε₁δ₂ ≡̂ μ-ε ε₂δ₂ of ⌊μ⌋-b b')
                  ≡
                  [ ℓ ↦' μ-ε argδ ] CLam (⌊μ⌋-b b) (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b')
    CLam≡-distr
      = begin

          CLam (⌊μ⌋-b b) (μ-ε ε₁δ₂ ≡̂ μ-ε ε₂δ₂ of ⌊μ⌋-b b')

        ≡⟨ cong (CLam _) (≡̂-subst³ ε₁δ-commutes ε₂δ-commutes (⌊μ⌋-b-sub-id (suc k) _ _)) ⟩

          CLam (⌊μ⌋-b b) (([ ℓ ↦' μ-ε argδ ] μ-ε ε₁δ₁) ≡̂ ([ ℓ ↦' μ-ε argδ ] μ-ε ε₂δ₁) of ([ ℓ ↦' μ-ε argδ ] ⌊μ⌋-b b'))

        ≡˘⟨ cong (CLam _) (≡̂-↦'-distr ℓ (μ-ε argδ) (μ-ε ε₁δ₁) (μ-ε ε₂δ₁) (⌊μ⌋-b b')) ⟩

          CLam (⌊μ⌋-b b) ([ ℓ ↦' μ-ε argδ ] (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b'))

        ≡⟨ cong (λ τ → CLam τ ([ ℓ ↦' μ-ε argδ ] (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b'))) (⌊μ⌋-b-sub-id k _ _) ⟩

          CLam ([ ℓ ↦' μ-ε argδ ] ⌊μ⌋-b b) ([ ℓ ↦' μ-ε argδ ] (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b'))

        ≡˘⟨ CLam-↦'-distr ℓ _ (⌊μ⌋-b b) (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b') ⟩

          [ ℓ ↦' μ-ε argδ ] CLam (⌊μ⌋-b b) (μ-ε ε₁δ₁ ≡̂ μ-ε ε₂δ₁ of ⌊μ⌋-b b')

        ∎
  μ-τ-sub-commutes {ℓ = ℓ} {k = k} Δ argδ (TWF-Conj ρ₁δ₁ ρ₂δ₁) (TWF-Conj ρ₁δ₂ ρ₂δ₂)
    = trans
        rec-commutes
        (sym (×-↦'-distr _ (μ-ε argδ) (μ-τ ρ₁δ₁) (μ-τ ρ₂δ₁)))
    where
    rec-commutes : ⟨ μ-τ ρ₁δ₂ × μ-τ ρ₂δ₂ ⟩ ≡ ⟨ ([ ℓ ↦' μ-ε argδ ] μ-τ ρ₁δ₁) × ([ ℓ ↦' μ-ε argδ ] μ-τ ρ₂δ₁) ⟩
    rec-commutes
      rewrite μ-τ-sub-commutes Δ argδ ρ₁δ₁ ρ₁δ₂
            | μ-τ-sub-commutes Δ argδ ρ₂δ₁ ρ₂δ₂
            = refl
  μ-τ-sub-commutes {ℓ = ℓ} {k = k} {εˢ = εˢ} Δ argδ (TWF-Arr {τ₂ = τ₂} argδ₁ resδ₁) (TWF-Arr argδ₂ resδ₂)
    = begin
        CΠ (μ-τ argδ₂) (μ-τ resδ₂)
      ≡⟨ cong (λ argδ → CΠ argδ (μ-τ resδ₂)) (μ-τ-sub-commutes Δ argδ argδ₁ argδ₂) ⟩
        CΠ ([ ℓ ↦' μ-ε argδ ] μ-τ argδ₁) (μ-τ resδ₂)
      ≡⟨ cong (CΠ _) resδ-subst-massage ⟩
        CΠ ([ ℓ ↦' μ-ε argδ ] μ-τ argδ₁) ([ ℓ ↦' μ-ε argδ ] μ-τ resδ₁)
      ≡˘⟨ CS.CΠ-↦'-distr ℓ _ (μ-τ argδ₁) (μ-τ resδ₁) ⟩
        ([ ℓ ↦' μ-ε argδ ] CΠ (μ-τ argδ₁) (μ-τ resδ₁))
      ∎
    where
    resδ-subst-massage : μ-τ resδ₂ ≡ [ ℓ ↦' μ-ε argδ ] μ-τ resδ₁
    resδ-subst-massage
      rewrite SS.act-τ-extensionality (SS.ext-replace-comm (SR.weaken-ε-k k εˢ) (SS.ctx-idx k)) τ₂
            | SR.act-ε-distr (raise k) suc εˢ
            = μ-τ-sub-commutes (Δ , _) argδ resδ₁ resδ₂
  μ-τ-sub-commutes Δ argδ (TWF-ADT consδs₁) (TWF-ADT consδs₂) = {! !}

μ-τ-sub-front-commutes : {Γˢ : S.Ctx ℓ}
                       → (argδ : Γˢ ⊢[ E of κ ] ε₂ˢ ⦂ τ₁ˢ)
                       → (codδ : Γˢ , τ₁ˢ ⊢[ E ] τ₂ˢ)
                       → (resτδ : Γˢ ⊢[ E ] [ zero ↦τ ε₂ˢ ] τ₂ˢ)
                       → μ-τ resτδ ≡ [ zero ↦  μ-ε argδ ] μ-τ codδ
μ-τ-sub-front-commutes {ε₂ˢ = ε₂ˢ} {τ₂ˢ = τ₂ˢ} argδ codδ resτδ
  = let act-ε-refl = sym (SR.act-ε-id (λ _ → refl) ε₂ˢ)
        resτδ' = subst (λ ε → _ ⊢[ E ] [ zero ↦τ ε ] τ₂ˢ) act-ε-refl resτδ
     in trans (helper (cong ([ zero ↦τ_] τ₂ˢ) act-ε-refl) resτδ resτδ') (μ-τ-sub-commutes [ _ ] argδ codδ resτδ')
  where
  helper : {τ₁ τ₂ : SType ℓ}
         → τ₁ ≡ τ₂
         → (Γ⊢τ₁ : Γˢ ⊢[ E ] τ₁)
         → (Γ⊢τ₂ : Γˢ ⊢[ E ] τ₂)
         → μ-τ Γ⊢τ₁ ≡ μ-τ Γ⊢τ₂
  helper refl Γ⊢τ₁ Γ⊢τ₂ = cong μ-τ (unique-Γ⊢τ Γ⊢τ₁ Γ⊢τ₂)
