{-# OPTIONS --safe #-}

module Surface.WellScoped.Renaming where

open import Data.Fin using (zero; suc; raise)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat using (_+_; zero; suc)
open import Data.Vec
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import Surface.WellScoped
open import Surface.WellScoped.Actions (record { Target = Fin
                                               ; var-action = λ r idx → SVar (r idx)
                                               ; ext = λ where _ zero → zero
                                                               r (suc n) → suc (r n)
                                               }) public

weaken-τ : SType ℓ → SType (suc ℓ)
weaken-τ = act-τ suc

weaken-ε : STerm ℓ → STerm (suc ℓ)
weaken-ε = act-ε suc

weaken-τ-k : ∀ k → SType ℓ → SType (k + ℓ)
weaken-τ-k k = act-τ (raise k)

weaken-ε-k : ∀ k → STerm ℓ → STerm (k + ℓ)
weaken-ε-k k = act-ε (raise k)


≡-ext : {f₁ f₂ : Fin ℓ → Fin ℓ'}
      → (∀ x → f₁ x ≡ f₂ x)
      → (∀ x → ext f₁ x ≡ ext f₂ x)
≡-ext _ zero = refl
≡-ext x-≡ (suc x) rewrite x-≡ x = refl

var-action-cong : {f₁ f₂ : Fin ℓ → Fin ℓ'}
                → (∀ x → f₁ x ≡ f₂ x)
                → (∀ x → var-action f₁ x ≡ var-action f₂ x)
var-action-cong x-≡ x rewrite x-≡ x = refl

open import Surface.WellScoped.ActionsLemmas var-action-record
                                             record { ≡-ext = ≡-ext
                                                    ; var-action-cong = var-action-cong
                                                    }
                                             public

-- Renaming using an identity function is an identity
ActIdentity : {Ty : ℕ → Set} → ActionOn Ty → Set
ActIdentity {Ty} act = ∀ {ℓ} {f : Fin ℓ → Fin ℓ}
                       → (∀ x → f x ≡ x)
                       → (v : Ty ℓ)
                       → act f v ≡ v

ext-id : ∀ {f : Fin ℓ → Fin ℓ}
       → (∀ x → f x ≡ x)
       → (∀ x → ext f x ≡ x)
ext-id f-≡ zero = refl
ext-id f-≡ (suc x) rewrite f-≡ x = refl

act-τ-id : ActIdentity act-τ
act-ρ-id : ActIdentity act-ρ
act-ε-id : ActIdentity act-ε
act-cons-id : ActIdentity {ADTCons nₐ} act-cons
act-branches-id : ActIdentity {CaseBranches nₐ} act-branches

act-τ-id f-id ⟨ b ∣ ρ ⟩ rewrite act-ρ-id (ext-id f-id) ρ = refl
act-τ-id f-id (τ₁ ⇒ τ₂) rewrite act-τ-id f-id τ₁
                              | act-τ-id (ext-id f-id) τ₂ = refl
act-τ-id f-id (⊍ cons) rewrite act-cons-id f-id cons = refl

act-ρ-id f-id (ε₁ ≈ ε₂) rewrite act-ε-id f-id ε₁
                              | act-ε-id f-id ε₂ = refl
act-ρ-id f-id (ρ₁ ∧ ρ₂) rewrite act-ρ-id f-id ρ₁
                              | act-ρ-id f-id ρ₂ = refl

act-ε-id f-id SUnit = refl
act-ε-id f-id (SVar idx) rewrite f-id idx = refl
act-ε-id f-id (SLam τ ε) rewrite act-τ-id f-id τ
                               | act-ε-id (ext-id f-id) ε = refl
act-ε-id f-id (SApp ε₁ ε₂) rewrite act-ε-id f-id ε₁
                                 | act-ε-id f-id ε₂ = refl
act-ε-id f-id (SCase ε branches) rewrite act-ε-id f-id ε
                                       | act-branches-id f-id branches = refl
act-ε-id f-id (SCon idx ε cons) rewrite act-ε-id f-id ε
                                      | act-cons-id f-id cons = refl

act-cons-id f-id [] = refl
act-cons-id f-id (τ ∷ cons) rewrite act-τ-id f-id τ
                                  | act-cons-id f-id cons = refl

act-branches-id f-id [] = refl
act-branches-id f-id (MkCaseBranch body ∷ bs) rewrite act-ε-id (ext-id f-id) body
                                                    | act-branches-id f-id bs = refl


-- A composition of renamings is a renaming by the composition
ActDistributivity : {Ty : ℕ → Set} → ActionOn Ty → Set
ActDistributivity {Ty} act = ∀ {ℓ₀ ℓ₁ ℓ₂}
                             → (r₁ : Fin ℓ₀ → Fin ℓ₁)
                             → (r₂ : Fin ℓ₁ → Fin ℓ₂)
                             → (v : Ty ℓ₀)
                             → act r₂ (act r₁ v) ≡ act (r₂ ∘ r₁) v

ext-distr : (r₁ : Fin ℓ₀ → Fin ℓ₁)
          → (r₂ : Fin ℓ₁ → Fin ℓ₂)
          → ∀ x
          → ext r₂ (ext r₁ x) ≡ ext (λ x → r₂ (r₁ x)) x
ext-distr _ _ zero = refl
ext-distr _ _ (suc x) = refl

act-τ-distr : ActDistributivity act-τ
act-ρ-distr : ActDistributivity act-ρ
act-ε-distr : ActDistributivity act-ε
act-cons-distr : ActDistributivity {ADTCons nₐ} act-cons
act-branches-distr : ActDistributivity {CaseBranches nₐ} act-branches

act-τ-distr r₁ r₂ ⟨ b ∣ ρ ⟩ rewrite act-ρ-distr (ext r₁) (ext r₂) ρ
                                  | act-ρ-extensionality (ext-distr r₁ r₂) ρ = refl
act-τ-distr r₁ r₂ (τ₁ ⇒ τ₂) rewrite act-τ-distr r₁ r₂ τ₁
                                  | act-τ-distr (ext r₁) (ext r₂) τ₂
                                  | act-τ-extensionality (ext-distr r₁ r₂) τ₂ = refl
act-τ-distr r₁ r₂ (⊍ cons) rewrite act-cons-distr r₁ r₂ cons = refl

act-ρ-distr r₁ r₂ (ε₁ ≈ ε₂) rewrite act-ε-distr r₁ r₂ ε₁
                                  | act-ε-distr r₁ r₂ ε₂ = refl
act-ρ-distr r₁ r₂ (ρ₁ ∧ ρ₂) rewrite act-ρ-distr r₁ r₂ ρ₁
                                  | act-ρ-distr r₁ r₂ ρ₂ = refl

act-ε-distr r₁ r₂ SUnit = refl
act-ε-distr r₁ r₂ (SVar idx) = refl
act-ε-distr r₁ r₂ (SLam τ ε) rewrite act-τ-distr r₁ r₂ τ
                                   | act-ε-distr (ext r₁) (ext r₂) ε
                                   | act-ε-extensionality (ext-distr r₁ r₂) ε = refl
act-ε-distr r₁ r₂ (SApp ε₁ ε₂) rewrite act-ε-distr r₁ r₂ ε₁
                                     | act-ε-distr r₁ r₂ ε₂ = refl
act-ε-distr r₁ r₂ (SCase ε branches) rewrite act-ε-distr r₁ r₂ ε
                                           | act-branches-distr r₁ r₂ branches = refl
act-ε-distr r₁ r₂ (SCon idx ε cons) rewrite act-ε-distr r₁ r₂ ε
                                          | act-cons-distr r₁ r₂ cons = refl

act-cons-distr r₁ r₂ [] = refl
act-cons-distr r₁ r₂ (τ ∷ τs) rewrite act-τ-distr r₁ r₂ τ
                                    | act-cons-distr r₁ r₂ τs = refl

act-branches-distr r₁ r₂ [] = refl
act-branches-distr r₁ r₂ (MkCaseBranch body ∷ bs) rewrite act-ε-distr (ext r₁) (ext r₂) body
                                                        | act-branches-distr r₁ r₂ bs
                                                        | act-ε-extensionality (ext-distr r₁ r₂) body = refl


weaken-τ-comm : ∀ (ρ : Fin ℓ → Fin ℓ') (τ : SType ℓ)
              → act-τ (ext ρ) (weaken-τ τ) ≡ weaken-τ (act-τ ρ τ)
weaken-τ-comm ρ τ rewrite act-τ-distr suc (ext ρ) τ
                        | act-τ-distr ρ suc τ = refl

weaken-ε-comm : ∀ (ρ : Fin ℓ → Fin ℓ') (ε : STerm ℓ)
              → act-ε (ext ρ) (weaken-ε ε) ≡ weaken-ε (act-ε ρ ε)
weaken-ε-comm ρ ε rewrite act-ε-distr suc (ext ρ) ε
                        | act-ε-distr ρ suc ε = refl


-- Renamings are injective
open import Surface.WellScoped.SyntaxInjectivity

Injective : {A B : Set} → (A → B) → Set
Injective f = ∀ {x₁ x₂}
              → f x₁ ≡ f x₂
              → x₁ ≡ x₂

ext-inj : {f : Fin ℓ → Fin ℓ'}
        → Injective f
        → Injective (ext f)
ext-inj f-inj {zero} {zero} ext-≡ = refl
ext-inj f-inj {suc x₁} {suc x₂} ext-≡ rewrite f-inj (suc-injective ext-≡) = refl

ActInjectivity : {Ty : ℕ → Set} → ActionOn Ty → Set
ActInjectivity {Ty} act = ∀ {ℓ ℓ'} {f : Fin ℓ → Target ℓ'}
                          → Injective f
                          → Injective (act f)

act-τ-injectivity : ActInjectivity act-τ
act-ρ-injectivity : ActInjectivity act-ρ
act-ε-injectivity : ActInjectivity act-ε
act-cons-injectivity : ActInjectivity {ADTCons nₐ} act-cons
act-branches-injectivity : ActInjectivity {CaseBranches nₐ} act-branches

act-τ-injectivity f-inj {⟨ b₁ ∣ ρ₁ ⟩} {⟨ b₂ ∣ ρ₂ ⟩} ≡-prf rewrite ⟨∣⟩-inj₁ ≡-prf
                                                                | act-ρ-injectivity (ext-inj f-inj) (⟨∣⟩-inj₂ ≡-prf) = refl
act-τ-injectivity f-inj {x₁₁ ⇒ x₁₂} {x₂₁ ⇒ x₂₂} ≡-prf rewrite act-τ-injectivity f-inj (⇒-inj₁ ≡-prf)
                                                            | act-τ-injectivity (ext-inj f-inj) (⇒-inj₂ ≡-prf) = refl
act-τ-injectivity f-inj {⊍ cons₁} {⊍ cons₂} ≡-prf with ⊍-inj-len ≡-prf
... | refl rewrite act-cons-injectivity f-inj (⊍-inj-cons ≡-prf) = refl

act-ρ-injectivity f-inj {ε₁₁ ≈ ε₁₂} {ε₂₁ ≈ ε₂₂} ≡-prf rewrite act-ε-injectivity f-inj {ε₁₁} {ε₂₁} (≈-inj₁ ≡-prf)
                                                            | act-ε-injectivity f-inj {ε₁₂} {ε₂₂} (≈-inj₂ ≡-prf) = refl
act-ρ-injectivity f-inj {ρ₁₁ ∧ ρ₁₂} {ρ₂₁ ∧ ρ₂₂} ≡-prf rewrite act-ρ-injectivity f-inj (∧-inj₁ ≡-prf)
                                                            | act-ρ-injectivity f-inj (∧-inj₂ ≡-prf) = refl

act-ε-injectivity f-inj {SUnit} {SUnit} ≡-prf = refl
act-ε-injectivity f-inj {SVar ι₁} {SVar ι₂} ≡-prf rewrite f-inj (SVar-inj ≡-prf) = refl
act-ε-injectivity f-inj {SLam τ₁ ε₁} {SLam τ₂ ε₂} ≡-prf rewrite act-τ-injectivity f-inj (SLam-inj₁ ≡-prf)
                                                              | act-ε-injectivity (ext-inj f-inj) {ε₁} {ε₂} (SLam-inj₂ ≡-prf) = refl
act-ε-injectivity f-inj {SApp ε₁₁ ε₁₂} {SApp ε₂₁ ε₂₂} ≡-prf rewrite act-ε-injectivity f-inj {ε₁₁} {ε₂₁} (SApp-inj₁ ≡-prf)
                                                                  | act-ε-injectivity f-inj {ε₁₂} {ε₂₂} (SApp-inj₂ ≡-prf) = refl
act-ε-injectivity f-inj {SCase ε₁ branches₁} {SCase ε₂ branches₂} ≡-prf with SCase-inj-len ≡-prf
... | refl rewrite act-ε-injectivity f-inj {ε₁} {ε₂} (SCase-inj₁ ≡-prf)
                 | act-branches-injectivity f-inj (SCase-inj₂ ≡-prf) = refl
act-ε-injectivity f-inj {SCon idx ε₁ cons₁} {SCon idx₁ ε₂ cons₂} ≡-prf with SCon-inj-len ≡-prf
... | refl rewrite SCon-inj₁ ≡-prf
                 | act-ε-injectivity f-inj {ε₁} {ε₂} (SCon-inj₂ ≡-prf)
                 | act-cons-injectivity f-inj (SCon-inj₃ ≡-prf) = refl

act-cons-injectivity f-inj {[]} {[]} ≡-prf = refl
act-cons-injectivity f-inj {τ₁ ∷ cons₁} {τ₂ ∷ cons₂} ≡-prf rewrite act-τ-injectivity f-inj (∷-inj₁ ≡-prf)
                                                                 | act-cons-injectivity f-inj (∷-inj₂ ≡-prf) = refl

act-branches-injectivity f-inj {[]} {[]} ≡-prf = refl
act-branches-injectivity f-inj {MkCaseBranch ε₁ ∷ bs₁} {MkCaseBranch ε₂ ∷ bs₂} ≡-prf
    rewrite act-ε-injectivity (ext-inj f-inj) {ε₁} {ε₂} (CaseBranch-inj (∷-inj₁ ≡-prf))
          | act-branches-injectivity f-inj (∷-inj₂ ≡-prf) = refl


weaken-τ-injective : Injective {SType ℓ} {SType (suc ℓ)} weaken-τ
weaken-τ-injective = act-τ-injectivity suc-injective

weaken-ε-injective : Injective {STerm ℓ} {STerm (suc ℓ)} weaken-ε
weaken-ε-injective = act-ε-injectivity suc-injective

weaken-τ-suc-k : ∀ k (τ : SType ℓ)
               → weaken-τ-k (suc k) τ ≡ weaken-τ (weaken-τ-k k τ)
weaken-τ-suc-k k τ = sym (act-τ-distr (raise k) suc τ)

weaken-ε-suc-k : ∀ k (ε : STerm ℓ)
               → weaken-ε-k (suc k) ε ≡ weaken-ε (weaken-ε-k k ε)
weaken-ε-suc-k k ε = sym (act-ε-distr (raise k) suc ε)
