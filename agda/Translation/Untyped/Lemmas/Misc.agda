{-# OPTIONS --safe #-}

module Translation.Untyped.Lemmas.Misc where

open import Data.Vec using (_∷_; []; lookup)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Common.Helpers
open import Common.Types
import Core.Syntax.Renaming as CR
open import Surface.Syntax as S
import Surface.Syntax.Renaming as SR

open import Translation.Untyped

exts-agree : (f : Fin ℓ → Fin ℓ')
           → SR.ext f f≡ CR.ext f
exts-agree f zero = refl
exts-agree f (suc x) = refl

infixl 10 _then_
_then_ : ∀ {S : Set} {a b c : S}
       → a ≡ b
       → b ≡ c
       → a ≡ c
refl then refl = refl

μ-lookup-commute : ∀ (cons : S.ADTCons nₐ ℓ) ι
                 → μ-τ-untyped (lookup cons ι) ≡ lookup (μ-cons-untyped cons) ι
μ-lookup-commute (τ ∷ _) zero = refl
μ-lookup-commute (_ ∷ cons) (suc ι) = μ-lookup-commute cons ι
