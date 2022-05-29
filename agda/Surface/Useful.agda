{-# OPTIONS --safe #-}

{- We prove our language is "useful" by showing that it is non-empty, and there are some useful typeable terms -}

module Surface.Useful where

open import Data.Fin using (Fin; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.Membership
open import Surface.Syntax.Renaming
open import Surface.Derivations.Declarative
open import Surface.Operational
open import Surface.Derivations.Declarative.Theorems.Thinning

unit : SType 0
unit = ⟨ BUnit ∣ Τ ⟩

unit-typeable : ⊘ ⊢[ φ ] SUnit ⦂ unit
unit-typeable = T-Unit TCTX-Empty


bool-cons : ADTCons (Mkℕₐ 2) 0
bool-cons = unit ∷ unit ∷ []

bool : SType 0
bool = ⊍ bool-cons

bool-wf : ⊘ ⊢[ φ ] bool
bool-wf = TWF-ADT (TWF-TrueRef TCTX-Empty ∷ TWF-TrueRef TCTX-Empty ∷ [])

false : STerm 0
false = SCon zero SUnit bool-cons

true : STerm 0
true = SCon (suc zero) SUnit bool-cons

false-typeable : ⊘ ⊢[ φ ] false ⦂ bool
false-typeable = T-Con refl unit-typeable bool-wf

true-typeable : ⊘ ⊢[ φ ] true ⦂ bool
true-typeable = T-Con refl unit-typeable bool-wf


not : STerm 0
not = SLam
        bool
        (SCase (SVar zero)
            (MkCaseBranch (weaken-ε-k 2 true)
           ∷ MkCaseBranch (weaken-ε-k 2 false)
           ∷ []))

bool-fun : SType 0
bool-fun = bool ⇒ weaken-τ bool

bool-wf-weaken : ⊘ , bool ⊢[ φ ] weaken-τ bool
bool-wf-weaken = Γ⊢τ-weakening TCTX-Empty bool-wf bool-wf

bool-fun-wf : ⊘ ⊢[ φ ] bool-fun
bool-fun-wf = TWF-Arr bool-wf bool-wf-weaken

bool-ctx-ok : (⊘ , bool) ok[ φ ]
bool-ctx-ok = TCTX-Bind TCTX-Empty bool-wf

not-typeable : ⊘ ⊢[ φ ] not ⦂ bool-fun
not-typeable =
  T-Abs
    bool-fun-wf
    (T-Case
      bool-wf-weaken
      (T-Var bool-ctx-ok (∈-zero refl))
      (OneMoreBranch
        (Γ⊢ε⦂τ-weakening
          bool-ctx-ok
          (Γ⊢τ-weakening TCTX-Empty bool-wf (TWF-TrueRef TCTX-Empty))
          (T-Con
            refl
            (T-Unit bool-ctx-ok)
            (Γ⊢τ-weakening TCTX-Empty bool-wf bool-wf)
          )
        )
        (OneMoreBranch
          (Γ⊢ε⦂τ-weakening
            bool-ctx-ok
            (Γ⊢τ-weakening TCTX-Empty bool-wf (TWF-TrueRef TCTX-Empty))
            (T-Con
              refl
              (T-Unit bool-ctx-ok)
              (Γ⊢τ-weakening TCTX-Empty bool-wf bool-wf)
            )
          )
          NoBranches
        )
      )
    )

not-true-is-false : SApp not true ↝⋆ false
not-true-is-false =
  ↝-trans
    (E-AppAbs)
    (↝-trans
      (E-CaseMatch IV-Unit (suc zero))
      ↝-refl
    )


bool-inhabitants : ⊘ ⊢[ φ ] ε ⦂ τ
                 → τ ≡ bool
                 → IsValue ε
                 → ε ≡ false ⊎ ε ≡ true
bool-inhabitants (T-Con ≡-prf Γ adtτ) τ-≡ iv = {! !}
bool-inhabitants (T-Sub Γ τ'δ <:) τ-≡ iv = {! !}
