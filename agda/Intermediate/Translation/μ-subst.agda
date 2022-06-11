{-# OPTIONS --safe #-}

open import Intermediate.Oracle
open import Intermediate.Translation.θ-Props renaming (Props to T-Props)
open import Intermediate.Derivations.Algorithmic.Theorems.Substitution.θ-Props renaming (Props to S-Props)

module Intermediate.Translation.μ-subst(θ : Oracle)(θ-μ-props : T-Props θ)(θ-σ-props : S-Props θ) where

open import Data.Fin.Base using (zero; suc; raise)
open import Data.Nat.Base using (zero; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; subst; sym; trans; cong)
open Eq.≡-Reasoning

open import Common.Helpers
open import Data.Fin.Extra

open import Core.Syntax as C renaming (Γ to Γᶜ; ε to εᶜ; τ to τᶜ)
open import Core.Syntax.Derived as C
open import Core.Syntax.Renaming as CR
open import Core.Syntax.Renaming.Distributivity as CR
open import Core.Syntax.Substitution as CS
open import Core.Syntax.Substitution.Distributivity as CS
open import Core.Syntax.Derived.Substitution as CS
open import Core.Derivations as C renaming (_⊢_⦂_ to _⊢ᶜ_⦂_)
open import Intermediate.Syntax as I renaming (Γ to Γⁱ;
                                               τ to τⁱ; τ' to τ'ⁱ; σ to σⁱ;
                                               τ₁ to τ₁ⁱ; τ₁' to τ₁'ⁱ;
                                               τ₂ to τ₂ⁱ; τ₂' to τ₂'ⁱ;
                                               ε to εⁱ; ε' to ε'ⁱ; ε₁ to ε₁ⁱ; ε₂ to ε₂ⁱ)

open import Intermediate.Syntax.CtxSuffix as I
open import Intermediate.Syntax.Renaming as IR
open import Intermediate.Syntax.Substitution as IS
open import Intermediate.Syntax.Substitution.Distributivity as IS
open import Intermediate.Derivations.Algorithmic as I hiding (θ)
open import Intermediate.Derivations.Algorithmic.Theorems.Agreement
open import Intermediate.Derivations.Algorithmic.Theorems.Substitution(θ)(θ-σ-props)
open import Intermediate.Derivations.Algorithmic.Theorems.Thinning
open import Intermediate.Derivations.Algorithmic.Theorems.Uniqueness

open import Intermediate.Translation.SubstUnique
open import Intermediate.Translation.Typed
open import Intermediate.Translation.Untyped
open import Intermediate.Translation.μ-weakening
open import Intermediate.Translation.μ-subst.Helpers

⌊μ⌋-b-sub-id : ∀ k ε b
             → ⌊μ⌋-b {ℓ = k + ℓ} b ≡ [ ℓ ↦' ε ] (⌊μ⌋-b b)
⌊μ⌋-b-sub-id _ _ BUnit = refl

μ-Var-sub-distributes : (Δ : ,-CtxSuffix ℓ σⁱ k)
                      → (argδ : [ θ ] Γⁱ ⊢ εⁱ ⦂ σⁱ)
                      → (codδ : [ θ ] Γⁱ ,σ, Δ ⊢ IVar ι ⦂ τⁱ)
                      → (resδ : [ θ ] Γⁱ ++ [↦Δ εⁱ ] Δ ⊢ [ ℓ ↦ε< εⁱ ] IVar ι ⦂ [ ℓ ↦τ< εⁱ ] τⁱ)
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
  μ-ε-sub-distributes {k = k} {εⁱ = εⁱ} Δ argδ (T-Abs {ε = bodyδ} (TWF-Arr {τ₁ = τ₁ⁱ} {τ₂ = τ₂ⁱ} dom-dom-arrδ _) dom-argδ) (T-Abs (TWF-Arr cod-dom-arrδ _) cod-argδ)
    rewrite IS.act-ε-extensionality (IS.ext-replace-comm (IR.weaken-ε-k k εⁱ) (ctx-idx k)) bodyδ
          | IS.act-τ-extensionality (IS.ext-replace-comm (IR.weaken-ε-k k εⁱ) (ctx-idx k)) τ₂ⁱ
          | IR.act-ε-distr (raise k) suc εⁱ
          | μ-τ-sub-distributes Δ         argδ dom-dom-arrδ cod-dom-arrδ
          | μ-ε-sub-distributes (Δ , τ₁ⁱ) argδ dom-argδ     cod-argδ
          | CS.act-ε-extensionality (CS.ext-replace-comm (CR.weaken-ε-k k (μ-ε argδ)) (ctx-idx k)) (μ-ε dom-argδ)
          = refl
  μ-ε-sub-distributes Δ argδ (T-App funδ₁ argδ₁ _ _) (T-App funδ₂ argδ₂ _ _)
    rewrite μ-ε-sub-distributes-any-τ Δ argδ argδ₁ argδ₂
          | μ-ε-sub-distributes-any-τ Δ argδ funδ₁ funδ₂
          = refl
  μ-ε-sub-distributes Δ argδ (T-Case resδ₁ domδ₁ branchesδ₁) (T-Case resδ₂ domδ₂ branchesδ₂)
    with refl ← typing-uniqueness domδ₂ (sub-Γ⊢ε⦂τ Δ argδ domδ₁)
    rewrite μ-ε-sub-distributes Δ argδ domδ₁ domδ₂
          | μ-branches-sub-distributes Δ argδ branchesδ₁ branchesδ₂
          = refl
  μ-ε-sub-distributes {k = k} {εⁱ = εⁱ} Δ argδ (T-Con {ι = ι} {cons = cons} refl domδ₁ (TWF-ADT consδs₁))
                                               (T-Con refl domδ₂ (TWF-ADT consδs₂))
    rewrite sym (IS.cons-lookup-comm (IS.replace-at (ctx-idx k) (IR.weaken-ε-k k εⁱ)) ι cons)
          | μ-ε-sub-distributes Δ argδ domδ₁ domδ₂
          | μ-cons-sub-distributes Δ argδ consδs₁ consδs₂
          = refl
  μ-ε-sub-distributes Δ argδ (T-SubW <:₁ εδ₁) (T-SubW <:₂ εδ₂)
    rewrite μ-ε-sub-distributes-any-τ Δ argδ εδ₁ εδ₂
          | sym (typing-uniqueness (sub-Γ⊢ε⦂τ Δ argδ εδ₁) εδ₂)
          | μ-<:-sub-distributes Δ argδ <:₁ <:₂
          = refl

  μ-<:-sub-distributes-ext : (Δ : ,-CtxSuffix ℓ σⁱ k)
                           → (argδ : [ θ ] Γⁱ ⊢ εⁱ ⦂ σⁱ)
                           → (cod-<: : [ θ ] Γⁱ ,σ, Δ , τ₁'ⁱ ⊢ τ₂'ⁱ <: τ₂ⁱ)
                           → (res-<: : [ θ ] Γⁱ ++ [↦Δ εⁱ ] (Δ  , τ₁'ⁱ)
                                           ⊢  IS.act-τ (IS.ext (IS.replace-at (ctx-idx k) (IR.weaken-ε-k k εⁱ))) τ₂'ⁱ
                                           <: IS.act-τ (IS.ext (IS.replace-at (ctx-idx k) (IR.weaken-ε-k k εⁱ))) τ₂ⁱ)
                           → μ-<: res-<: ≡ [ ℓ ↦' μ-ε argδ ] μ-<: cod-<:
  μ-<:-sub-distributes-ext {k = k} {εⁱ = εⁱ} {τ₂'ⁱ = τ₂'ⁱ} {τ₂ⁱ = τ₂ⁱ} Δ argδ cod-<: res-<:
    with ext-replace-comm ← IS.ext-replace-comm (IR.weaken-ε-k k εⁱ) (ctx-idx k)
    rewrite IS.act-τ-extensionality ext-replace-comm τ₂ⁱ
          | IS.act-τ-extensionality ext-replace-comm τ₂'ⁱ
          | IR.act-ε-distr (raise k) suc εⁱ
          = μ-<:-sub-distributes (Δ , _) argδ cod-<: res-<:

  μ-<:-sub-distributes : (Δ : ,-CtxSuffix ℓ σⁱ k)
                       → (argδ : [ θ ] Γⁱ ⊢ εⁱ ⦂ σⁱ)
                       → (cod-<: : [ θ ] Γⁱ ,σ, Δ ⊢ τ'ⁱ <: τⁱ)
                       → (res-<: : [ θ ] Γⁱ ++ [↦Δ εⁱ ] Δ ⊢ [ ℓ ↦τ< εⁱ ] τ'ⁱ <: [ ℓ ↦τ< εⁱ ] τⁱ )
                       → μ-<: res-<: ≡ [ ℓ ↦' μ-ε argδ ] μ-<: cod-<:
  μ-<:-sub-distributes {k = k} {εⁱ = εⁱ} Δ argδ (ST-Base {ρ₁ = ρ₁} {ρ₂ = ρ₂} is-just₁ _ _) (ST-Base is-just₂ _ _)
    rewrite IS.act-ρ-extensionality (IS.ext-replace-comm (IR.act-ε (raise k) εⁱ) (ctx-idx k)) ρ₁
          | IS.act-ρ-extensionality (IS.ext-replace-comm (IR.act-ε (raise k) εⁱ) (ctx-idx k)) ρ₂
          | IR.act-ε-distr (raise k) suc εⁱ
          = T-Props.sub-<: θ-μ-props Δ argδ is-just₁ is-just₂
  μ-<:-sub-distributes {ℓ = ℓ} {k = k} {εⁱ = εⁱ} Δ argδ
                      (ST-Arr {τ₂' = τ₂'ⁱ} {τ₂ = τ₂ⁱ} cod-<:₁ cod-<:₂ cod-τ₁⇒τ₂'δ cod-τ₁'⇒τ₂δ@(TWF-Arr cod-τ₁'δ _))
                      (ST-Arr                         res-<:₁ res-<:₂ res-τ₁⇒τ₂'δ res-τ₁'⇒τ₂δ@(TWF-Arr res-τ₁'δ _))
    rewrite μ-τ-sub-distributes Δ argδ cod-τ₁⇒τ₂'δ res-τ₁⇒τ₂'δ
          | μ-τ-sub-distributes Δ argδ cod-τ₁'δ res-τ₁'δ
          | μ-<:-sub-distributes Δ argδ cod-<:₁ res-<:₁
          | μ-<:-sub-distributes-ext Δ argδ cod-<:₂ res-<:₂

          | CS.ρ-σ-distr-ε suc (CS.replace-at (ctx-idx k) (CR.weaken-ε-k k (μ-ε argδ))) (μ-τ cod-τ₁'δ)
          | CS.σ-ρ-distr-ε (CS.ext (CS.replace-at (ctx-idx k) (CR.weaken-ε-k k (μ-ε argδ)))) suc (μ-τ cod-τ₁'δ)

          | CS.ρ-σ-distr-ε (CR.ext suc) (CS.replace-at (suc (ctx-idx k)) (CR.act-ε suc (CR.weaken-ε-k k (μ-ε argδ)))) (μ-<: cod-<:₂)
          | CS.σ-ρ-distr-ε (CS.ext (CS.ext (CS.replace-at (ctx-idx k) (CR.weaken-ε-k k (μ-ε argδ))))) (CR.ext suc) (μ-<: cod-<:₂)
          | CS.act-ε-extensionality (act-ε-lemma₁ (ctx-idx k) (CR.weaken-ε-k k (μ-ε argδ))) (μ-<: cod-<:₂)

          | CR.act-ε-distr suc suc ([ ℓ ↦' μ-ε argδ ] (μ-<: cod-<:₁))
          | CR.act-ε-distr suc suc (μ-<: cod-<:₁)
          | CS.σ-ρ-distr-ε (CS.ext (CS.ext (CS.replace-at (ctx-idx k) (CR.weaken-ε-k k (μ-ε argδ))))) (λ ι → suc (suc ι)) (μ-<: cod-<:₁)
          | CS.ρ-σ-distr-ε (λ ι → suc (suc ι)) (CS.replace-at (ctx-idx k) (CR.weaken-ε-k k (μ-ε argδ))) (μ-<: cod-<:₁)
          | CS.act-ε-extensionality (λ x → CR.act-ε-distr suc suc (CS.replace-at (ctx-idx k) (CR.weaken-ε-k k (μ-ε argδ)) x)) (μ-<: cod-<:₁)
          = refl

  μ-ε-sub-distributes-any-τ : (Δ : ,-CtxSuffix ℓ σⁱ k)
                            → (argδ : [ θ ] Γⁱ ⊢ εⁱ ⦂ σⁱ)
                            → (codδ : [ θ ] Γⁱ ,σ, Δ ⊢ ε'ⁱ ⦂ τⁱ)
                            → (resδ : [ θ ] Γⁱ ++ [↦Δ εⁱ ] Δ ⊢ [ ℓ ↦ε< εⁱ ] ε'ⁱ ⦂ τ'ⁱ)
                            → μ-ε resδ ≡ [ ℓ ↦' μ-ε argδ ] μ-ε codδ
  μ-ε-sub-distributes-any-τ Δ argδ codδ resδ
    = let resδ' = sub-Γ⊢ε⦂τ Δ argδ codδ
       in trans (μ-ε-cong-unique resδ resδ') (μ-ε-sub-distributes Δ argδ codδ resδ')

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
  μ-τ-sub-distributes Δ argδ (TWF-ADT consδs₁) (TWF-ADT consδs₂) = cong CADT (μ-cons-sub-distributes Δ argδ consδs₁ consδs₂)

  μ-cons-sub-distributes : (Δ : ,-CtxSuffix ℓ σⁱ k)
                         → (argδ : [ θ ] Γⁱ ⊢ εⁱ ⦂ σⁱ)
                         → {cons : I.ADTCons nₐ (suc k + ℓ)}
                         → (codδs : All ([ θ ] Γⁱ ,σ, Δ ⊢_) cons)
                         → (resδs : All ([ θ ] Γⁱ ++ [↦Δ εⁱ ] Δ ⊢_) ([ ℓ ↦c< εⁱ ] cons))
                         → μ-cons resδs ≡ [ ℓ ↦c' μ-ε argδ ] μ-cons codδs
  μ-cons-sub-distributes Δ argδ [] [] = refl
  μ-cons-sub-distributes Δ argδ (codδ ∷ codδs) (resδ ∷ resδs)
    rewrite μ-τ-sub-distributes Δ argδ codδ resδ
          | μ-cons-sub-distributes Δ argδ codδs resδs
          = refl

  μ-branches-sub-distributes : (Δ : ,-CtxSuffix ℓ σⁱ k)
                             → (argδ : [ θ ] Γⁱ ⊢ εⁱ ⦂ σⁱ)
                             → {cons : I.ADTCons nₐ (suc k + ℓ)}
                             → {bs : I.CaseBranches nₐ (suc k + ℓ)}
                             → (codδs : I.BranchesHaveType θ (Γⁱ ,σ, Δ) cons bs τⁱ)
                             → (resδs : I.BranchesHaveType θ (Γⁱ ++ [↦Δ εⁱ ] Δ) ([ ℓ ↦c< εⁱ ] cons) ([ ℓ ↦bs< εⁱ ] bs) ([ ℓ ↦τ< εⁱ ] τⁱ))
                             → μ-branches resδs ≡ [ ℓ ↦bs' μ-ε argδ ] μ-branches codδs
  μ-branches-sub-distributes Δ argδ NoBranches NoBranches = refl
  μ-branches-sub-distributes Δ argδ (OneMoreBranch codδ codδs) (OneMoreBranch resδ resδs)
    rewrite μ-branches-sub-distributes Δ argδ codδs resδs
          = refl
    -- TODO right now this doesn't handle proper proofs for path sensitivity,
    -- so this (meta)proof will break once they are added.

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
  helper : {τ₁ τ₂ : IType ℓ}
         → τ₁ ≡ τ₂
         → (Γ⊢τ₁ : [ θ ] Γⁱ ⊢ τ₁)
         → (Γ⊢τ₂ : [ θ ] Γⁱ ⊢ τ₂)
         → μ-τ Γ⊢τ₁ ≡ μ-τ Γ⊢τ₂
  helper refl Γ⊢τ₁ Γ⊢τ₂ = cong μ-τ (unique-Γ⊢τ Γ⊢τ₁ Γ⊢τ₂)
