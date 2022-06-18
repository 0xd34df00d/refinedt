module Surface.Derivations.Algorithmic.ToIntermediate.Translation where

open import Data.Fin using (suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax as S
import Surface.Syntax.Substitution as S
open import Surface.Derivations.Algorithmic as S
open import Surface.Derivations.Algorithmic.Theorems.Agreement

open import Intermediate.Syntax as I
open import Intermediate.Syntax.Short
open import Intermediate.Syntax.Renaming as IR
import Intermediate.Derivations.Algorithmic as I

open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Aliases
open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Subst
open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Typed
