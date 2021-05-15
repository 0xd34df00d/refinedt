{-# OPTIONS --safe #-}

{- We prove our language is "useful" by showing that it is non-empty, and there are some useful typeable terms -}

module Surface.Useful where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.Membership
open import Surface.Syntax.Renaming
open import Surface.Derivations
open import Surface.Operational
open import Surface.Operational.BetaEquivalence
open import Surface.Theorems.Thinning

Typeable : STerm 0 → Set
Typeable ε = Σ (SType 0) (λ τ → ⊘ ⊢ ε ⦂ τ)

unit : SType 0
unit = ⟨ BUnit ∣ SUnit ≈ SUnit of BUnit ⟩

unit-typeable : ⊘ ⊢ SUnit ⦂ unit
unit-typeable = T-Unit TCTX-Empty


bool-cons : ADTCons (Mkℕₐ 2) 0
bool-cons = unit ∷ unit ∷ []

bool : SType 0
bool = ⊍ bool-cons

bool-wf : ⊘ ⊢ bool
bool-wf = TWF-ADT (TWF-TrueRef TCTX-Empty ∷ TWF-TrueRef TCTX-Empty ∷ [])

false : STerm 0
false = SCon zero SUnit bool-cons

true : STerm 0
true = SCon (suc zero) SUnit bool-cons

false-typeable : ⊘ ⊢ false ⦂ bool
false-typeable = T-Con refl unit-typeable bool-wf

true-typeable : ⊘ ⊢ true ⦂ bool
true-typeable = T-Con refl unit-typeable bool-wf


not : STerm 0
not = SLam bool (SCase (SVar zero)
        (MkCaseBranch (weaken-ε-k 2 true)
       ∷ MkCaseBranch (weaken-ε-k 2 false)
       ∷ []))

bool-fun : SType 0
bool-fun = bool ⇒ weaken-τ bool

bool-wf-weaken : ⊘ , bool ⊢ weaken-τ bool
bool-wf-weaken = twf-weakening TCTX-Empty bool-wf bool-wf

bool-fun-wf : ⊘ ⊢ bool-fun
bool-fun-wf = TWF-Arr bool-wf bool-wf-weaken

bool-ctx-ok : (⊘ , bool) ok
bool-ctx-ok = TCTX-Bind TCTX-Empty bool-wf

not-typeable : ⊘ ⊢ not ⦂ bool-fun
not-typeable =
  T-Abs
    bool-fun-wf
    (T-Case
      bool-wf-weaken
      (T-Var bool-ctx-ok (∈-zero refl))
      (OneMoreBranch
        (t-weakening
          bool-ctx-ok
          (twf-weakening TCTX-Empty bool-wf (TWF-TrueRef TCTX-Empty))
          (T-Con
            refl
            (T-Unit bool-ctx-ok)
            (twf-weakening TCTX-Empty bool-wf bool-wf)
          )
        )
        (OneMoreBranch
          (t-weakening
            bool-ctx-ok
            (twf-weakening TCTX-Empty bool-wf (TWF-TrueRef TCTX-Empty))
            (T-Con
              refl
              (T-Unit bool-ctx-ok)
              (twf-weakening TCTX-Empty bool-wf bool-wf)
            )
          )
          NoBranches
        )
      )
    )
