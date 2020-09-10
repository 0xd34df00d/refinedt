module Surface.Theorems.Thinning where

open import Data.Vec.Relation.Unary.All renaming (map to All-map)

open import Surface.Syntax
open import Surface.Derivations
open import Sublist

private
  arr-wf-dom : Γ ⊢' SArr x τ₁ τ₂ → Γ ⊢' τ₁
  arr-wf-dom (TWF-Arr domδ _) = domδ

abstract
  twf-thinning : Γ ⊂ Γ' → Γ' ok → (Γ ⊢' τ)    → (Γ' ⊢' τ)
  t-thinning   : Γ ⊂ Γ' → Γ' ok → (Γ ⊢ ε ⦂ τ) → (Γ' ⊢ ε ⦂ τ)

  twf-thinning ⊂-prf Γ'ok (TWF-TrueRef _) = TWF-TrueRef Γ'ok
  twf-thinning ⊂-prf Γ'ok (TWF-Base ε₁δ ε₂δ) = let expCtxOk = TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)
                                                in TWF-Base (t-thinning (PrependBoth ⊂-prf) expCtxOk ε₁δ) (t-thinning (PrependBoth ⊂-prf) expCtxOk ε₂δ)
  twf-thinning ⊂-prf Γ'ok (TWF-Conj ρ₁ ρ₂) = TWF-Conj (twf-thinning ⊂-prf Γ'ok ρ₁) (twf-thinning ⊂-prf Γ'ok ρ₂)
  twf-thinning ⊂-prf Γ'ok (TWF-Arr argδ resδ) = TWF-Arr
                                                  (twf-thinning ⊂-prf Γ'ok argδ)
                                                  (twf-thinning (PrependBoth ⊂-prf) (TCTX-Bind Γ'ok (twf-thinning ⊂-prf Γ'ok argδ)) resδ)
  twf-thinning {Γ} {Γ'} ⊂-prf Γ'ok (TWF-ADT consδs)= TWF-ADT (map-cons consδs)
    where
      map-cons : {cons : ADTCons n} → All (Γ ⊢'_) cons → All (Γ' ⊢'_) cons
      map-cons [] = []
      map-cons (px ∷ pxs) = twf-thinning ⊂-prf Γ'ok px ∷ map-cons pxs

  t-thinning ⊂-prf Γ'ok (T-Unit gok) = T-Unit Γ'ok
  t-thinning ⊂-prf Γ'ok (T-Var gok x) = T-Var Γ'ok (⊂-preserves-∈ ⊂-prf x)
  t-thinning ⊂-prf Γ'ok (T-Abs arrδ bodyδ) = let arrδ' = twf-thinning ⊂-prf Γ'ok arrδ
                                                 bodyδ'-ok = TCTX-Bind Γ'ok (arr-wf-dom arrδ')
                                                 bodyδ' = t-thinning (PrependBoth ⊂-prf) bodyδ'-ok bodyδ
                                              in T-Abs arrδ' bodyδ'
  t-thinning ⊂-prf Γ'ok (T-App δ₁ δ₂) = T-App (t-thinning ⊂-prf Γ'ok δ₁) (t-thinning ⊂-prf Γ'ok δ₂)
  t-thinning {Γ} {Γ'} ⊂-prf Γ'ok (T-Case resδ scrut branches) = T-Case (twf-thinning ⊂-prf Γ'ok resδ) (t-thinning ⊂-prf Γ'ok scrut) (thin-branches branches)
    where
      thin-branches : ∀ {τ cons} {bs : CaseBranches n} → BranchesHaveType Γ cons bs τ → BranchesHaveType Γ' cons bs τ
      thin-branches NoBranches = NoBranches
      thin-branches (OneMoreBranch εδ bs) = OneMoreBranch {! !} (thin-branches bs)

  t-thinning ⊂-prf Γ'ok (T-Con conArg adtτ) = T-Con (t-thinning ⊂-prf Γ'ok conArg) (twf-thinning ⊂-prf Γ'ok adtτ)
  t-thinning ⊂-prf Γ'ok (T-Sub x x₁) = {! !}
