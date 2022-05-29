{-# OPTIONS --allow-unsolved-metas #-}

module Surface.Translation.μ-subst where

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
open import Surface.Syntax as S renaming (Γ to Γˢ;
                                          τ to τˢ; τ' to τ'ˢ; τ₁ to τ₁ˢ; τ₁' to τ₁'ˢ; τ₂ to τ₂ˢ;
                                          σ to σˢ; σ' to σ'ˢ;
                                          ε to εˢ; ε' to ε'ˢ; ε₁ to ε₁ˢ; ε₂ to ε₂ˢ)
open import Surface.Syntax.CtxSuffix as S
open import Surface.Syntax.Renaming as SR
open import Surface.Syntax.Substitution as SS
open import Surface.Derivations.Algorithmic as S
open import Surface.Derivations.Algorithmic.Theorems.Agreement
open import Surface.Derivations.Algorithmic.Theorems.Thinning
open import Surface.Derivations.Algorithmic.Theorems.Uniqueness

open import Surface.Translation.SubstUnique
open import Surface.Translation.Typed
open import Surface.Translation.Untyped
open import Surface.Translation.μ-weakening

⌊μ⌋-b-sub-id : ∀ k ε b
             → ⌊μ⌋-b {ℓ = k + ℓ} b ≡ [ ℓ ↦' ε ] (⌊μ⌋-b b)
⌊μ⌋-b-sub-id _ _ BUnit = refl

μ-Var-sub-distributes : (Δ : ,-CtxSuffix ℓ σˢ k)
                      → (argδ : Γˢ ⊢[ θ , E of not-t-sub ] εˢ ⦂ σ'ˢ)
                      → (<:δ  : Γˢ ⊢[ θ , E ] σ'ˢ <: σˢ)
                      → (codδ : Γˢ ,σ, Δ ⊢[ θ , E of not-t-sub ] SVar ι ⦂ τˢ)
                      → (resδ : Γˢ ++ [↦Δ εˢ ] Δ ⊢[ θ , E of not-t-sub ] [ ℓ ↦ε< εˢ ] SVar ι ⦂ [ ℓ ↦τ< εˢ ] τˢ)
                      → μ-ε resδ ≡ [ ℓ ↦' μ-ε argδ ] μ-ε codδ
μ-Var-sub-distributes {k = k} Δ argδ <:δ (T-Var {ι = ι} Γok ∈) resδ with ctx-idx k <>? ι | resδ
... | less _ | T-Var _ _ = refl
... | greater _ | T-Var _ _ = refl
... | equal refl | resδ = trans
                            (μ-ε-cong-unique resδ (Γ⊢ε⦂τ-weakening-suffix (Γ⊢ε⦂τ-⇒-Γok resδ) argδ))
                            (μ-ε-weakening-suffix-commutes _ argδ)

mutual
  μ-ε-sub-distributes : (Δ : ,-CtxSuffix ℓ σˢ k)
                      → (argδ : Γˢ ⊢[ θ , E of not-t-sub ] εˢ ⦂ σ'ˢ)
                      → (<:δ  : Γˢ ⊢[ θ , E ] σ'ˢ <: σˢ)
                      → (codδ : Γˢ ,σ, Δ ⊢[ θ , E of κ' ] ε'ˢ ⦂ τˢ)
                      → (resδ : Γˢ ++ [↦Δ εˢ ] Δ ⊢[ θ , E of κ' ] [ ℓ ↦ε< εˢ ] ε'ˢ ⦂ [ ℓ ↦τ< εˢ ] τˢ)
                      → μ-ε resδ ≡ [ ℓ ↦' μ-ε argδ ] μ-ε codδ
  μ-ε-sub-distributes Δ argδ <:δ (T-Unit _) (T-Unit _) = refl
  μ-ε-sub-distributes Δ argδ <:δ codδ@(T-Var _ _) resδ = μ-Var-sub-distributes Δ argδ <:δ codδ resδ
  μ-ε-sub-distributes Δ argδ <:δ (T-Abs dom-arrδ dom-argδ) (T-Abs cod-arrδ cod-argδ) = {! !}
  μ-ε-sub-distributes Δ argδ <:δ (T-App domδ domδ₁ resτ-≡ resτδ) codδ = {! !}
  μ-ε-sub-distributes Δ argδ <:δ (T-Case resδ domδ branches-well-typed) codδ = {! !}
  μ-ε-sub-distributes Δ argδ <:δ (T-Con ≡-prf domδ adtτ) codδ = {! !}
  μ-ε-sub-distributes Δ argδ <:δ (T-Sub domδ τ'δ <:) codδ = {! !}

  μ-τ-sub-distributes : (Δ : ,-CtxSuffix ℓ σˢ k)
                      → (argδ : Γˢ ⊢[ θ , E of not-t-sub ] εˢ ⦂ σ'ˢ)
                      → (<:δ  : Γˢ ⊢[ θ , E ] σ'ˢ <: σˢ)
                      → (codδ : Γˢ ,σ, Δ ⊢[ θ , E ] τˢ)
                      → (resδ : Γˢ ++ [↦Δ εˢ ] Δ ⊢[ θ , E ] [ ℓ ↦τ< εˢ ] τˢ)
                      → μ-τ resδ ≡ [ ℓ ↦' μ-ε argδ ] μ-τ codδ
  μ-τ-sub-distributes {k = k} Δ argδ <:δ (TWF-TrueRef Γok) (TWF-TrueRef Γok₂) = ⌊μ⌋-b-sub-id k _ _
  μ-τ-sub-distributes {ℓ = ℓ} {k = k} {εˢ = εˢ} Δ argδ <:δ (TWF-Base {b = b} {ε₁ = ε₁} {b' = b'} {ε₂ = ε₂} ε₁δ₁ ε₂δ₁) (TWF-Base ε₁δ₂ ε₂δ₂)
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
      rewrite SS.act-ε-extensionality (SS.ext-replace-comm (SR.weaken-ε-k k εˢ) (ctx-idx k)) ε₁
            | SR.act-ε-distr (raise k) suc εˢ
            = μ-ε-sub-distributes (Δ , _) argδ <:δ ε₁δ₁ ε₁δ₂

    ε₂δ-distributes : μ-ε ε₂δ₂ ≡ [ ℓ ↦' μ-ε argδ ] μ-ε ε₂δ₁
    ε₂δ-distributes
      rewrite SS.act-ε-extensionality (SS.ext-replace-comm (SR.weaken-ε-k k εˢ) (ctx-idx k)) ε₂
            | SR.act-ε-distr (raise k) suc εˢ
            = μ-ε-sub-distributes (Δ , _) argδ <:δ ε₂δ₁ ε₂δ₂

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
  μ-τ-sub-distributes {ℓ = ℓ} {k = k} Δ argδ <:δ (TWF-Conj ρ₁δ₁ ρ₂δ₁) (TWF-Conj ρ₁δ₂ ρ₂δ₂)
    = trans
        rec-distributes
        (sym (×-↦'-distr _ (μ-ε argδ) (μ-τ ρ₁δ₁) (μ-τ ρ₂δ₁)))
    where
    rec-distributes : ⟨ μ-τ ρ₁δ₂ × μ-τ ρ₂δ₂ ⟩ ≡ ⟨ ([ ℓ ↦' μ-ε argδ ] μ-τ ρ₁δ₁) × ([ ℓ ↦' μ-ε argδ ] μ-τ ρ₂δ₁) ⟩
    rec-distributes
      rewrite μ-τ-sub-distributes Δ argδ <:δ ρ₁δ₁ ρ₁δ₂
            | μ-τ-sub-distributes Δ argδ <:δ ρ₂δ₁ ρ₂δ₂
            = refl
  μ-τ-sub-distributes {ℓ = ℓ} {k = k} {εˢ = εˢ} Δ argδ <:δ (TWF-Arr {τ₂ = τ₂} argδ₁ resδ₁) (TWF-Arr argδ₂ resδ₂)
    = begin
        CΠ (μ-τ argδ₂) (μ-τ resδ₂)
      ≡⟨ cong (λ argδ → CΠ argδ (μ-τ resδ₂)) (μ-τ-sub-distributes Δ argδ <:δ argδ₁ argδ₂) ⟩
        CΠ ([ ℓ ↦' μ-ε argδ ] μ-τ argδ₁) (μ-τ resδ₂)
      ≡⟨ cong (CΠ _) resδ-subst-massage ⟩
        CΠ ([ ℓ ↦' μ-ε argδ ] μ-τ argδ₁) ([ ℓ ↦' μ-ε argδ ] μ-τ resδ₁)
      ≡˘⟨ CS.CΠ-↦'-distr ℓ _ (μ-τ argδ₁) (μ-τ resδ₁) ⟩
        ([ ℓ ↦' μ-ε argδ ] CΠ (μ-τ argδ₁) (μ-τ resδ₁))
      ∎
    where
    resδ-subst-massage : μ-τ resδ₂ ≡ [ ℓ ↦' μ-ε argδ ] μ-τ resδ₁
    resδ-subst-massage
      rewrite SS.act-τ-extensionality (SS.ext-replace-comm (SR.weaken-ε-k k εˢ) (ctx-idx k)) τ₂
            | SR.act-ε-distr (raise k) suc εˢ
            = μ-τ-sub-distributes (Δ , _) argδ <:δ resδ₁ resδ₂
  μ-τ-sub-distributes Δ argδ <:δ (TWF-ADT consδs₁) (TWF-ADT consδs₂) = {! !}

μ-τ-sub-front-distributes : {Γˢ : S.Ctx ℓ}
                          → (argδ : Γˢ ⊢[ θ , E of not-t-sub ] ε₂ˢ ⦂ τ₁'ˢ)
                          → (<:δ  : Γˢ ⊢[ θ , E ] τ₁'ˢ <: τ₁ˢ)
                          → (codδ : Γˢ , τ₁ˢ ⊢[ θ , E ] τ₂ˢ)
                          → (resτδ : Γˢ ⊢[ θ , E ] [ zero ↦τ ε₂ˢ ] τ₂ˢ)
                          → μ-τ resτδ ≡ [ zero ↦  μ-ε argδ ] μ-τ codδ
μ-τ-sub-front-distributes {θ = θ} {ε₂ˢ = ε₂ˢ} {τ₂ˢ = τ₂ˢ} argδ <:δ codδ resτδ
  = let act-ε-refl = sym (SR.act-ε-id (λ _ → refl) ε₂ˢ)
        resτδ' = subst (λ ε → _ ⊢[ θ , E ] [ zero ↦τ ε ] τ₂ˢ) act-ε-refl resτδ
     in trans (helper (cong ([ zero ↦τ_] τ₂ˢ) act-ε-refl) resτδ resτδ') (μ-τ-sub-distributes [ _ ] argδ <:δ codδ resτδ')
  where
  helper : {τ₁ τ₂ : SType ℓ}
         → τ₁ ≡ τ₂
         → (Γ⊢τ₁ : Γˢ ⊢[ θ , E ] τ₁)
         → (Γ⊢τ₂ : Γˢ ⊢[ θ , E ] τ₂)
         → μ-τ Γ⊢τ₁ ≡ μ-τ Γ⊢τ₂
  helper refl Γ⊢τ₁ Γ⊢τ₂ = cong μ-τ (unique-Γ⊢τ Γ⊢τ₁ Γ⊢τ₂)
