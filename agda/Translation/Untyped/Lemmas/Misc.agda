{-# OPTIONS --safe #-}

module Translation.Untyped.Lemmas.Misc where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Common.Helpers
open import Common.Types
import Core.Syntax.Renaming as CR
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
