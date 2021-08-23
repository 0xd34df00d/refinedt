{-# OPTIONS --safe #-}

module Translation.μ-weakening.Helpers where

open import Data.Fin using (zero; suc)
open import Data.Nat.Base
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Helpers

open import Core.Syntax as C renaming (Γ to Γᶜ; ε to εᶜ)
open import Core.Syntax.Renaming as CR
open import Core.Syntax.Renaming.Distributivity as CR
open import Core.Syntax.Derived as CR
open import Core.Syntax.Derived.Renaming as CR
open import Core.Operational as C
open import Surface.Syntax as S using (BUnit)

open import Translation.Untyped

⌊μ⌋-b-weaken-id : ∀ k b
                → ⌊μ⌋-b b ≡ act-ε (ext-k' {ℓ} k suc) (⌊μ⌋-b b)
⌊μ⌋-b-weaken-id _ BUnit = refl

⌊μ⌋-b-act-id : ∀ ℓ (f : Fin ℓ → Fin ℓ') b
             → CR.act-ε f (⌊μ⌋-b {ℓ} b) ≡ ⌊μ⌋-b b
⌊μ⌋-b-act-id _ _ BUnit = refl

lemma₁ : ∀ k (ε : CExpr (1 + k + ℓ))
       → (act-ε (ext-k' 3 suc)
           (act-ε (ext-k' 3 suc)
             (act-ε suc (act-ε suc (act-ε (ext-k' (1 + k) suc) ε)))))
         ≡
         (act-ε (ext-k' (5 + k) suc)
           (act-ε (ext-k' 3 suc)
             (act-ε (ext-k' 3 suc) (act-ε suc (act-ε suc ε)))))
lemma₁ k ε
  rewrite act-ε-distr suc suc ε
        | act-ε-distr (λ ι → suc (suc ι)) (ext-k' 3 suc) ε
        | act-ε-distr (λ ι → suc (suc (ext suc ι))) (ext-k' 3 suc) ε
        | act-ε-distr (λ ι → suc (suc (ext suc (ext suc ι)))) (ext-k' (5 + k) suc) ε
     -- |
        | act-ε-distr (ext-k' (1 + k) suc) suc ε
        | act-ε-distr (λ ι → suc (ext (ext-k' k suc) ι)) suc ε
        | act-ε-distr (λ ι → suc (suc (ext (ext-k' k suc) ι))) (ext-k' 3 suc) ε
        | act-ε-distr (λ ι → suc (suc (ext suc (ext (ext-k' k suc) ι)))) (ext-k' 3 suc) ε
        = CR.act-ε-extensionality (λ where zero → refl
                                           (suc _) → refl
                                  ) ε
