module Surface.Theorems.Thinning where

open import Data.Nat.Base
open import Data.Nat.Induction
open import Data.Nat.Properties

open import Surface.Syntax
open import Surface.Derivations
open import Surface.Derivations.WF
open import Surface.Theorems.TCTX
open import Surface.Theorems.Helpers

open import Sublist

private
  arr-wf-dom : Γ ⊢ SArr x τ₁ τ₂ → Γ ⊢ τ₁
  arr-wf-dom (TWF-Arr domδ _) = domδ

  size-lemma₁ : (δ : (Γ , x ⦂ τ') ⊢ ε ⦂ τ) → size-twf (Γok-head (Γ⊢ε⦂τ-⇒-Γok δ)) < suc (size-t δ <> n)

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
  t-thinning {Γ} {Γ'} ⊂-prf Γ'ok (T-Case resδ scrut branches) (acc rec) =
    let recAcc = rec (size-bs branches) (s≤s (k≤m<>n<>k (size-t scrut) (size-twf resδ) (size-bs branches)))
     in T-Case (twf-thinning ⊂-prf Γ'ok resδ {! !}) (t-thinning ⊂-prf Γ'ok scrut {! !}) (thin-branches branches recAcc)
    where
      thin-branches : ∀ {τ cons} {bs : CaseBranches n} → (δ : BranchesHaveType Γ cons bs τ) → Acc _<_ (size-bs δ) → BranchesHaveType Γ' cons bs τ
      thin-branches NoBranches _ = NoBranches
      thin-branches (OneMoreBranch εδ rest) (acc rec') =
        let branch-Γ-ok = Γ⊢ε⦂τ-⇒-Γok εδ
            rec1 = rec' (size-twf (Γok-head (Γ⊢ε⦂τ-⇒-Γok εδ))) (size-lemma₁ εδ)
            rec2 = rec' (size-t εδ) (s≤s (m≤m<>n (size-t εδ) (size-bs rest)))
            rec3 = rec' (size-bs rest) (s≤s (n≤m<>n (size-t εδ) (size-bs rest)))
            branch'-Γ-ok = TCTX-Bind Γ'ok (twf-thinning ⊂-prf Γ'ok (Γok-head branch-Γ-ok) rec1)
         in OneMoreBranch (t-thinning (PrependBoth ⊂-prf) branch'-Γ-ok εδ rec2) (thin-branches rest rec3)
  t-thinning ⊂-prf Γ'ok (T-Con conArg adtτ) _ = T-Con (t-thinning ⊂-prf Γ'ok conArg {! !}) (twf-thinning ⊂-prf Γ'ok adtτ {! !})
  t-thinning ⊂-prf Γ'ok (T-Sub x x₁) _ = {! !}
