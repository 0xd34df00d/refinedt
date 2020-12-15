{-# OPTIONS --safe #-}

module Surface.WellScoped.Substitution.Stable where

open import Data.Fin using (Fin; suc; zero; toℕ; raise)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Fin.Extra
open import Surface.WellScoped
open import Surface.WellScoped.Substitution
import Surface.WellScoped.Renaming as R
open import Surface.WellScoped.FreeVars

replace-suc-id : ∀ k (ε : STerm (k + ℓ)) (ι : Fin (k + ℓ))
               → ctx-idx k < suc ι
               → replace-at (ctx-idx k) ε (suc ι) ≡ SVar ι
replace-suc-id k ε ι var-is-far rewrite <>?-< var-is-far = refl

increased-vars-are-far-ε : ∀ k (b : Fin (suc k + ℓ)) (ε : STerm ℓ) (ι : Fin (k + ℓ)) {f : Fin ℓ → Fin (k + ℓ)}
                         → (∀ ι → b < suc ι → ι free-in-ε ε → f ι ≡ raise k ι)
                         → ι free-in-ε R.act-ε f ε
                         → ctx-idx {ℓ} k < suc ι
increased-vars-are-far-ε k b SUnit ι f-k-incr ()
increased-vars-are-far-ε k b (SVar idx) .(_ idx) f-k-incr free-SVar = {! !}
increased-vars-are-far-ε k b (SLam τ ε) ι f-k-incr (free-SLam-τ x) = {! !}
increased-vars-are-far-ε k b (SLam τ ε) ι {f} f-k-incr (free-SLam-ε free) =
  let rec = increased-vars-are-far-ε k (suc {! !}) ε {! !} {f = {! ext f !}} {! !} {! !}
   in {! !}
increased-vars-are-far-ε k b (SApp ε₁ ε₂) ι f-k-incr (free-SApp x) = {! !}
increased-vars-are-far-ε k b (SCase ε branches) ι f-k-incr (free-SCase x) = {! !}
increased-vars-are-far-ε k b (SCon idx ε adt-cons) ι f-k-incr (free-SCon x) = {! !}

{-
weakened-vars-are-far-ε : ∀ k (ε : STerm ℓ) (ι : Fin (k + ℓ))
                        → ι free-in-ε R.weaken-ε-k k ε
                        → ctx-idx {ℓ} k < suc ι
weakened-vars-are-far-ε k ε ι free = increased-vars-are-far-ε k zero ε ι (λ ι _ _ → refl) free
-}

{-
weakened-vars-are-far-τ : ∀ k (τ : SType ℓ) (ι : Fin (k + ℓ))
                        → ι free-in-τ R.weaken-τ-k k τ
                        → ctx-idx {ℓ} k < suc ι
weakened-vars-are-far-τ k ⟨ b ∣ ρ ⟩ ι (free-⟨∣⟩ x) = {! !}
weakened-vars-are-far-τ k (τ₁ ⇒ τ₂) ι (free-⇒ x) = {! !}
weakened-vars-are-far-τ k (⊍ cons) ι (free-⊍ x) = {! !}

weakened-vars-are-far-ε : ∀ k (ε : STerm ℓ) (ι : Fin (k + ℓ))
                        → ι free-in-ε R.weaken-ε-k k ε
                        → ctx-idx {ℓ} k < suc ι
weakened-vars-are-far-ε k (SVar idx) ι free-SVar = {! !}
weakened-vars-are-far-ε k (SLam τ ε) ι (free-SLam-τ free-τ) = weakened-vars-are-far-τ k τ ι free-τ
weakened-vars-are-far-ε k (SLam τ ε) ι (free-SLam-ε free-ε) = let rec = weakened-vars-are-far-ε {! !} {! !} {! !} {! !} in {! !}
weakened-vars-are-far-ε k (SApp ε₁ ε₂) ι (free-SApp (inj₁ free-ε₁)) = weakened-vars-are-far-ε k ε₁ ι free-ε₁
weakened-vars-are-far-ε k (SApp ε₁ ε₂) ι (free-SApp (inj₂ free-ε₂)) = weakened-vars-are-far-ε k ε₂ ι free-ε₂
weakened-vars-are-far-ε k (SCase ε branches) ι (free-SCase (inj₁ free-ε)) = weakened-vars-are-far-ε k ε ι free-ε
weakened-vars-are-far-ε k (SCase ε branches) ι (free-SCase (inj₂ free-branches)) = {! !}
weakened-vars-are-far-ε k (SCon idx ε cons) ι (free-SCon (inj₁ free-ε)) = weakened-vars-are-far-ε k ε ι free-ε
weakened-vars-are-far-ε k (SCon idx ε cons) ι (free-SCon (inj₂ free-cons)) = {! !}
-}

f-ext-stable-SLam : ∀ {ε : STerm (suc ℓ)} {f : Fin ℓ → STerm ℓ}
                  → (∀ ι → ι free-in-ε SLam τ ε → f ι ≡ SVar ι)
                  → (∀ ι → ι free-in-ε ε → ext f ι ≡ SVar ι)
f-ext-stable-SLam f-stable zero free = refl
f-ext-stable-SLam f-stable (suc ι) free rewrite f-stable ι (free-SLam-ε free) = refl

act-τ-stable : ∀ (τ : SType ℓ) {f : Fin ℓ → STerm ℓ}
             → (∀ ι → ι free-in-τ τ → f ι ≡ SVar ι)
             → act-τ f τ ≡ τ
act-ρ-stable : ∀ (ρ : Refinement ℓ) {f : Fin ℓ → STerm ℓ}
             → (∀ ι → ι free-in-ρ ρ → f ι ≡ SVar ι)
             → act-ρ f ρ ≡ ρ
act-ε-stable : ∀ (ε : STerm ℓ) {f : Fin ℓ → STerm ℓ}
             → (∀ ι → ι free-in-ε ε → f ι ≡ SVar ι)
             → act-ε f ε ≡ ε

act-τ-stable τ f-stable = {! !}

act-ρ-stable ρ f-stable = {! !}

act-ε-stable SUnit f-stable = refl
act-ε-stable (SVar ι) f-stable = f-stable ι free-SVar
act-ε-stable (SLam τ ε) f-stable rewrite act-τ-stable τ (λ ι free-τ → f-stable ι (free-SLam-τ free-τ))
                                       | act-ε-stable ε (f-ext-stable-SLam f-stable) = refl
act-ε-stable (SApp ε₁ ε₂) f-stable rewrite act-ε-stable ε₁ (λ ι free-ε₁ → f-stable ι (free-SApp (inj₁ free-ε₁)))
                                         | act-ε-stable ε₂ (λ ι free-ε₂ → f-stable ι (free-SApp (inj₂ free-ε₂))) = refl
act-ε-stable (SCase ε branches) f-stable = {! !}
act-ε-stable (SCon idx ε adt-cons) f-stable = {! !}

{-
ReplaceFreeIdentity : {Ty : ℕ → Set} → R.ActionOn Ty → SubstOn Ty → Set
ReplaceFreeIdentity {Ty} ρ-act [_↦_]_ = ∀ {ℓ} k (ε₀ : STerm (k + ℓ)) (v : Ty (k + ℓ))
                                        → [ ctx-idx k ↦ ε₀ ] (ρ-act suc v) ≡ v

replace-free-τ : ReplaceFreeIdentity R.act-τ [_↦τ_]_
replace-free-ρ : ReplaceFreeIdentity R.act-ρ [_↦ρ_]_
replace-free-ε : ReplaceFreeIdentity R.act-ε [_↦ε_]_

replace-free-τ k ε₀ ⟨ b ∣ ρ ⟩ = {! !}
replace-free-τ k ε₀ (τ₁ ⇒ τ₂) = {! !}
replace-free-τ k ε₀ (⊍ cons) = {! !}

replace-free-ρ k ε₀ ρ = let rec = subst-rename-ρ-distr (replace-at (ctx-idx k) ε₀) suc ρ in {! !}

replace-free-ε k ε₀ SUnit = refl
replace-free-ε k ε₀ (SVar idx) with ctx-idx k <>? suc idx
... | less m<n = refl
... | equal m≡n = {! !}
... | greater m>n = {! !}
replace-free-ε k ε₀ (SLam τ ε) = {! !}
replace-free-ε k ε₀ (SApp ε ε₁) = {! !}
replace-free-ε k ε₀ (SCase ε branches) = {! !}
replace-free-ε k ε₀ (SCon idx ε adt-cons) = {! !}
-}


