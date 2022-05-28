{-# OPTIONS --safe #-}

module Intermediate.Translation.μ-weakening.Helpers where

open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Helpers

open import Core.Syntax
open import Core.Syntax.Renaming
open import Core.Syntax.Renaming.Distributivity
open import Intermediate.Syntax using (BUnit)

open import Intermediate.Translation.Untyped

⌊μ⌋-b-weaken-id : ∀ k b
                → ⌊μ⌋-b b ≡ act-ε (ext-k' {ℓ} k suc) (⌊μ⌋-b b)
⌊μ⌋-b-weaken-id _ BUnit = refl

⌊μ⌋-b-act-id : ∀ ℓ (f : Fin ℓ → Fin ℓ') b
             → act-ε f (⌊μ⌋-b {ℓ} b) ≡ ⌊μ⌋-b b
⌊μ⌋-b-act-id _ _ BUnit = refl

lemma₁ : ∀ k (ε : CExpr (1 + k + ℓ))
       → act-ε (ext-k' 3 suc)
           (act-ε (ext-k' 3 suc)
             (act-ε suc (act-ε suc (act-ε (ext-k' (1 + k) suc) ε))))
         ≡
         act-ε (ext-k' (5 + k) suc)
           (act-ε (ext-k' 3 suc)
             (act-ε (ext-k' 3 suc) (act-ε suc (act-ε suc ε))))
lemma₁ k ε
  rewrite act-ε-distr suc suc ε
        | act-ε-distr (λ ι → suc (suc ι)) (ext-k' 3 suc) ε
        | act-ε-distr (λ ι → suc (suc (ext suc ι))) (ext-k' 3 suc) ε
        | act-ε-distr (λ ι → suc (suc (ext suc (ext suc ι)))) (ext-k' (5 + k) suc) ε
     -- |
        | act-ε-distr (ext-k' (1 + k) suc) suc ε
        | act-ε-distr (λ ι → suc (ext-k' (1 + k) suc ι)) suc ε
        | act-ε-distr (λ ι → suc (suc (ext (ext-k' k suc) ι))) (ext-k' 3 suc) ε
        | act-ε-distr (λ ι → suc (suc (ext suc (ext (ext-k' k suc) ι)))) (ext-k' 3 suc) ε
        = act-ε-extensionality (λ where zero → refl; (suc _) → refl) ε

lemma₂ : ∀ k (ε : CExpr (1 + k + ℓ))
       → act-ε (ext-k' 4 suc)
           (act-ε (ext-k' 4 suc)
             (act-ε (ext suc)
               (act-ε suc (act-ε suc (act-ε (ext-k' (1 + k) suc) ε)))))
         ≡
         act-ε (ext-k' (6 + k) suc)
           (act-ε (ext-k' 4 suc)
             (act-ε (ext-k' 4 suc)
               (act-ε (ext suc) (act-ε suc (act-ε suc ε)))))
lemma₂ k ε
  rewrite act-ε-distr suc suc ε
        | act-ε-distr (λ ι → suc (suc ι)) (ext suc) ε
        | act-ε-distr (λ ι → suc (suc (suc ι))) (ext-k' 4 suc) ε
        | act-ε-distr (λ ι → suc (suc (suc (ext suc ι)))) (ext-k' 4 suc) ε
        | act-ε-distr (λ ι → suc (suc (suc (ext suc (ext suc ι))))) (ext-k' (6 + k) suc) ε
     -- |
        | act-ε-distr (ext-k' (1 + k) suc) suc ε
        | act-ε-distr (λ ι → suc (ext-k' (1 + k) suc ι)) suc ε
        | act-ε-distr (λ ι → suc (suc (ext-k' (1 + k) suc ι))) (ext suc) ε
        | act-ε-distr (λ ι → suc (suc (suc (ext-k' (1 + k) suc ι)))) (ext-k' 4 suc) ε
        | act-ε-distr (λ ι → suc (suc (suc (ext suc (ext-k' (1 + k) suc ι))))) (ext-k' 4 suc) ε
        = act-ε-extensionality (λ where zero → refl; (suc _) → refl) ε

lemma₃ : ∀ k (ε : CExpr (1 + k + ℓ))
       → act-ε (ext-k' 4 suc)
           (act-ε (ext-k' 4 suc)
             (act-ε suc
               (act-ε suc (act-ε suc (act-ε (ext-k' (1 + k) suc) ε)))))
         ≡
         act-ε (ext-k' (6 + k) suc)
           (act-ε (ext-k' 4 suc)
             (act-ε (ext-k' 4 suc)
               (act-ε suc (act-ε suc (act-ε suc ε)))))
lemma₃ k ε
  rewrite act-ε-distr suc suc ε
        | act-ε-distr (λ ι → suc (suc ι)) suc ε
        | act-ε-distr (λ ι → suc (suc (suc ι))) (ext-k' 4 suc) ε
        | act-ε-distr (λ ι → suc (suc (suc (ext suc ι)))) (ext-k' 4 suc) ε
        | act-ε-distr (λ ι → suc (suc (suc (ext suc (ext suc ι))))) (ext-k' (6 + k) suc) ε
     -- |
        | act-ε-distr (ext-k' (1 + k) suc) suc ε
        | act-ε-distr (λ ι → suc (ext-k' (1 + k) suc ι)) suc ε
        | act-ε-distr (λ ι → suc (suc (ext-k' (1 + k) suc ι))) suc ε
        | act-ε-distr (λ ι → suc (suc (suc (ext-k' (1 + k) suc ι)))) (ext-k' 4 suc) ε
        | act-ε-distr (λ ι → suc (suc (suc (ext suc (ext-k' (1 + k) suc ι))))) (ext-k' 4 suc) ε
        = act-ε-extensionality (λ where zero → refl; (suc _) → refl) ε

lemma₄ : ∀ k (ε : CExpr (1 + k + ℓ))
       → act-ε (ext-k' 5 suc)
           (act-ε (ext-k' 5 suc)
             (act-ε (ext suc)
               (act-ε (ext suc)
                 (act-ε suc
                   (act-ε suc (act-ε (ext-k' (1 + k) suc) ε))))))
         ≡
         act-ε (ext-k' (7 + k) suc)
           (act-ε (ext-k' 5 suc)
             (act-ε (ext-k' 5 suc)
               (act-ε (ext suc)
                 (act-ε (ext suc) (act-ε suc (act-ε suc ε))))))
lemma₄ k ε
  rewrite act-ε-distr suc suc ε
        | act-ε-distr (λ ι → suc (suc ι)) (ext suc) ε
        | act-ε-distr (λ ι → suc (suc (suc ι))) (ext suc) ε
        | act-ε-distr (λ ι → suc (suc (suc (suc ι)))) (ext-k' 5 suc) ε
        | act-ε-distr (λ ι → suc (suc (suc (suc (ext suc ι))))) (ext-k' 5 suc) ε
        | act-ε-distr (λ ι → suc (suc (suc (suc (ext suc (ext suc ι)))))) (ext-k' (7 + k) suc) ε
     -- |
        | act-ε-distr (ext-k' (1 + k) suc) suc ε
        | act-ε-distr (λ ι → suc (ext-k' (1 + k) suc ι)) suc ε
        | act-ε-distr (λ ι → suc (suc (ext-k' (1 + k) suc ι))) (ext suc) ε
        | act-ε-distr (λ ι → suc (suc (suc (ext-k' (1 + k) suc ι)))) (ext suc) ε
        | act-ε-distr (λ ι → suc (suc (suc (suc (ext-k' (1 + k) suc ι))))) (ext-k' 5 suc) ε
        | act-ε-distr (λ ι → suc (suc (suc (suc (ext suc (ext-k' (1 + k) suc ι)))))) (ext-k' 5 suc) ε
        = act-ε-extensionality (λ where zero → refl; (suc _) → refl) ε

lemma₅ : ∀ k (ε : CExpr (1 + k + ℓ))
       → act-ε (ext suc) (act-ε (ext-k' (1 + k) suc) ε)
         ≡
         act-ε (ext-k' (2 + k) suc) (act-ε (ext suc) ε)
lemma₅ k ε
  rewrite act-ε-distr (ext-k' (1 + k) suc) (ext suc) ε
        | act-ε-distr (ext suc) (ext-k' (2 + k) suc) ε
        = act-ε-extensionality (λ where zero → refl; (suc _) → refl) ε
