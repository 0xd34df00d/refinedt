open import Surface.Derivations.Algorithmic using (UniquenessOfOracles)

module Surface.Translation.Helpers(oracles-equal : UniquenessOfOracles) where

open import Data.Fin using (zero; suc)
open import Data.Vec using (Vec; _∷_; []; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)

open import Core.Syntax as C renaming (Γ to Γᶜ; ε to εᶜ; τ to τᶜ)
open import Core.Syntax.Membership as C renaming (_∈_at_ to _∈ᶜ_at_)
open import Surface.Syntax as S renaming (Γ to Γˢ; τ to τˢ; τ' to τ'ˢ; ε to εˢ)
open import Surface.Syntax.Membership as S renaming (_∈_at_ to _∈ˢ_at_)
open import Surface.Derivations.Algorithmic as S
open import Surface.Derivations.Algorithmic.Theorems.Agreement as S
open import Surface.Derivations.Algorithmic.Theorems.Uniqueness(oracles-equal)

open import Surface.Translation.Typed
open import Surface.Translation.SubstUnique(oracles-equal)
open import Surface.Translation.μ-weakening(oracles-equal)

μ-preserves-∈ : (Γok : Γˢ ok[ E ])
              → (∈ : τˢ ∈ˢ Γˢ at ι)
              → μ-τ (τ∈Γ-⇒-Γ⊢τ Γok ∈) ∈ᶜ μ-Γ Γok at ι
μ-preserves-∈ (TCTX-Bind Γok τδ) (∈-zero refl) = ∈-zero (μ-τ-weakening-commutes Γok τδ τδ)
μ-preserves-∈ (TCTX-Bind Γok τδ) (∈-suc refl ∈) = ∈-suc (μ-τ-weakening-commutes Γok τδ (τ∈Γ-⇒-Γ⊢τ Γok ∈)) (μ-preserves-∈ Γok ∈)

μ-lookup-commutes : ∀ ι
                  → {cons : S.ADTCons nₐ ℓ}
                  → (consδs : All (Γˢ ⊢[ E ]_) cons)
                  → (δ : Γˢ ⊢[ E ] lookup cons ι)
                  → μ-τ δ ≡ lookup (μ-cons consδs) ι
μ-lookup-commutes zero (δ' ∷ _) δ = cong μ-τ (unique-Γ⊢τ δ δ')
μ-lookup-commutes (suc ι) (_ ∷ consδs) δ = μ-lookup-commutes ι consδs δ

μ-Γ-distributes-over-, : (Γ,τδ : (Γˢ , τˢ) ok[ E ])
                       → (Γδ : Γˢ ok[ E ])
                       → (τδ : Γˢ ⊢[ E ] τˢ)
                       → μ-Γ Γ,τδ ≡ μ-Γ Γδ , μ-τ τδ
μ-Γ-distributes-over-, (TCTX-Bind Γδ₁ τδ₁) Γδ₂ τδ₂
  rewrite unique-Γok Γδ₁ Γδ₂
        | unique-Γ⊢τ τδ₁ τδ₂
        = refl
