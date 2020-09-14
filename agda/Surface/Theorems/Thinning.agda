module Surface.Theorems.Thinning where

open import Data.Nat.Base
open import Data.Nat.Induction
open import Surface.Syntax
open import Surface.Derivations
open import Surface.Derivations.WF
open import Surface.Theorems.TCTX
open import Surface.Theorems.Helpers
open import Sublist

private
  arr-wf-dom : Γ ⊢ SArr x τ₁ τ₂ → Γ ⊢ τ₁
  arr-wf-dom (TWF-Arr domδ _) = domδ

abstract
  twf-thinning : Γ ⊂ Γ' → Γ' ok → (δ : Γ ⊢ τ)     → Acc _<_ (size-twf δ) → (Γ' ⊢ τ)
  t-thinning   : Γ ⊂ Γ' → Γ' ok → (δ : Γ ⊢ ε ⦂ τ) → Acc _<_ (size-t δ)   → (Γ' ⊢ ε ⦂ τ)

  twf-thinning ⊂-prf Γ'ok (TWF-TrueRef _) _ = TWF-TrueRef Γ'ok
  twf-thinning ⊂-prf Γ'ok (TWF-Base ε₁δ ε₂δ) _ = let expCtxOk = TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)
                                                  in TWF-Base (t-thinning (PrependBoth ⊂-prf) expCtxOk ε₁δ (<-wellFounded _)) (t-thinning (PrependBoth ⊂-prf) expCtxOk ε₂δ (<-wellFounded _))
  twf-thinning ⊂-prf Γ'ok (TWF-Conj ρ₁ ρ₂) _ = TWF-Conj (twf-thinning ⊂-prf Γ'ok ρ₁ (<-wellFounded _)) (twf-thinning ⊂-prf Γ'ok ρ₂ (<-wellFounded _))
  twf-thinning ⊂-prf Γ'ok (TWF-Arr argδ resδ) _ = TWF-Arr
                                                    (twf-thinning ⊂-prf Γ'ok argδ (<-wellFounded _))
                                                    (twf-thinning (PrependBoth ⊂-prf) (TCTX-Bind Γ'ok (twf-thinning ⊂-prf Γ'ok argδ (<-wellFounded _))) resδ (<-wellFounded _))
  twf-thinning {Γ} {Γ'} ⊂-prf Γ'ok (TWF-ADT consδs) _ = TWF-ADT (map-cons consδs)
    where
      map-cons : {cons : ADTCons n} → All (Γ ⊢_) cons → All (Γ' ⊢_) cons
      map-cons [] = []
      map-cons (px ∷ pxs) = twf-thinning ⊂-prf Γ'ok px (<-wellFounded _) ∷ map-cons pxs

  t-thinning ⊂-prf Γ'ok (T-Unit gok) _ = T-Unit Γ'ok
  t-thinning ⊂-prf Γ'ok (T-Var gok x) _ = T-Var Γ'ok (⊂-preserves-∈ ⊂-prf x)
  t-thinning ⊂-prf Γ'ok (T-Abs arrδ bodyδ) _ = let arrδ' = twf-thinning ⊂-prf Γ'ok arrδ (<-wellFounded _)
                                                   bodyδ'-ok = TCTX-Bind Γ'ok (arr-wf-dom arrδ')
                                                   bodyδ' = t-thinning (PrependBoth ⊂-prf) bodyδ'-ok bodyδ (<-wellFounded _)
                                                in T-Abs arrδ' bodyδ'
  t-thinning ⊂-prf Γ'ok (T-App δ₁ δ₂) _ = T-App (t-thinning ⊂-prf Γ'ok δ₁ {! !}) (t-thinning ⊂-prf Γ'ok δ₂ (<-wellFounded _))
  t-thinning {Γ} {Γ'} ⊂-prf Γ'ok (T-Case resδ scrut branches) wf = T-Case (twf-thinning ⊂-prf Γ'ok resδ (<-wellFounded _)) (t-thinning ⊂-prf Γ'ok scrut (<-wellFounded _)) (thin-branches branches)
    where
      thin-branches : ∀ {τ cons} {bs : CaseBranches n} → BranchesHaveType Γ cons bs τ → BranchesHaveType Γ' cons bs τ
      thin-branches NoBranches = NoBranches
      thin-branches (OneMoreBranch εδ rest) =
        let branch-Γ-ok = Γ⊢ε⦂τ-⇒-Γok εδ
            branch'-Γ-ok = TCTX-Bind Γ'ok (twf-thinning ⊂-prf Γ'ok (Γok-head branch-Γ-ok) {! !})
         in OneMoreBranch (t-thinning (PrependBoth ⊂-prf) branch'-Γ-ok εδ {! !}) (thin-branches rest)
  t-thinning ⊂-prf Γ'ok (T-Con conArg adtτ) _ = T-Con (t-thinning ⊂-prf Γ'ok conArg (<-wellFounded _)) (twf-thinning ⊂-prf Γ'ok adtτ (<-wellFounded _))
  t-thinning ⊂-prf Γ'ok (T-Sub x x₁) _ = {! !}
