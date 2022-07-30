{-# OPTIONS --safe #-}

module Surface.Derivations.Common.Theorems.Substitution.Helpers where

open import Data.Fin.Base using (suc; zero)
open import Data.Nat.Base using (suc; zero; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Helpers
open import Data.Fin.Extra

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Membership
open import Surface.Syntax.Renaming as R
open import Surface.Syntax.Substitution as S
open import Surface.Syntax.Substitution.Distributivity as S
open import Surface.Syntax.Substitution.Stable

weaken-↦<-suc-comm-τ : ∀ {k ℓ}
                     → (τ : SType (suc k + ℓ))
                     → (ε : STerm ℓ)
                     → [ ℓ ↦τ< ε ] weaken-τ τ ≡ weaken-τ ([ ℓ ↦τ< ε ] τ)
weaken-↦<-suc-comm-τ {k} {ℓ} τ ε
  rewrite ρ-σ-distr-τ suc (replace-at (ctx-idx k) (weaken-ε-k k ε)) τ
        | σ-ρ-distr-τ (replace-at (suc (ctx-idx k)) (weaken-ε-k (suc k) ε)) suc τ
        | S.act-τ-extensionality (weaken-replace-comm (weaken-ε-k k ε) (ctx-idx k)) τ
        | weaken-ε-suc-k k ε
        = refl

var-earlier-in-Γ-remains : (Δ : ,-CtxSuffix ℓ σ k)
                         → τ ∈ Γ ,σ, Δ at ι
                         → (k<ι : ctx-idx k < ι)
                         → [ ℓ ↦τ< ε ] τ ∈ Γ ++ [↦Δ ε ] Δ at m<n-n-pred k<ι
var-earlier-in-Γ-remains {ε = ε} [ _ ] (∈-suc {τ = τ} refl ∈) (<-zero _)
  rewrite replace-weakened-τ-zero (R.weaken-ε-k zero ε) τ = ∈
var-earlier-in-Γ-remains {ι = (suc (suc _))} {ε = ε} (Δ , _) (∈-suc {τ = τ} refl ∈) (<-suc k<ι)
  = ∈-suc (weaken-↦<-suc-comm-τ _ ε) (var-earlier-in-Γ-remains Δ ∈ k<ι)

var-later-in-Γ-remains : (Δ : ,-CtxSuffix ℓ σ k)
                       → τ ∈ Γ ,σ, Δ at ι
                       → (k>ι : ctx-idx k > ι)
                       → [ ctx-idx k ↦τ R.weaken-ε-k k ε ] τ ∈ Γ ++ [↦Δ ε ] Δ at tighten k>ι
var-later-in-Γ-remains {ε = ε} (Δ , _) (∈-zero refl) (<-zero _) = ∈-zero (weaken-↦<-suc-comm-τ _ ε)
var-later-in-Γ-remains {ε = ε} (Δ , _) (∈-suc refl ∈) (<-suc k>ι) = ∈-suc (weaken-↦<-suc-comm-τ _ ε) (var-later-in-Γ-remains Δ ∈ k>ι)
