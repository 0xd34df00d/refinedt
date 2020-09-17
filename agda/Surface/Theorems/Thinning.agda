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

  size-lemma₁ : (n : ℕ) → (δ : (Γ , x ⦂ τ') ⊢ ε ⦂ τ) → size-twf (Γok-head (Γ⊢ε⦂τ-⇒-Γok δ)) < suc (size-t δ <> n)
  size-lemma₁ n δ = let r1 = Γok-head-smaller (Γ⊢ε⦂τ-⇒-Γok δ)
                        r2 = Γ⊢ε⦂τ-⇒-Γok-smaller δ
                        r3 = <-trans r1 r2
                     in <-trans r3 (s≤s (m≤m<>n (size-t δ) n))

private
  twf-thinning-sized : Γ ⊂ Γ' → Γ' ok → (δ : Γ ⊢ τ)         → Acc _<_ (size-twf δ) → (Γ' ⊢ τ)
  t-thinning-sized   : Γ ⊂ Γ' → Γ' ok → (δ : Γ ⊢ ε ⦂ τ)     → Acc _<_ (size-t δ)   → (Γ' ⊢ ε ⦂ τ)

  twf-thinning-sized ⊂-prf Γ'ok (TWF-TrueRef _) _ = TWF-TrueRef Γ'ok
  twf-thinning-sized ⊂-prf Γ'ok (TWF-Base ε₁δ ε₂δ) (acc rec) = let expCtxOk = TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)
                                                                   rec₁ = rec (size-t ε₁δ) (s≤s (m≤m<>n (size-t ε₁δ) (size-t ε₂δ)))
                                                                   rec₂ = rec (size-t ε₂δ) (s≤s (n≤m<>n (size-t ε₁δ) (size-t ε₂δ)))
                                                                in TWF-Base (t-thinning-sized (PrependBoth ⊂-prf) expCtxOk ε₁δ rec₁) (t-thinning-sized (PrependBoth ⊂-prf) expCtxOk ε₂δ rec₂)
  twf-thinning-sized ⊂-prf Γ'ok (TWF-Conj ρ₁ ρ₂) (acc rec) = let rec₁ = rec (size-twf ρ₁) (s≤s (m≤m<>n (size-twf ρ₁) (size-twf ρ₂)))
                                                                 rec₂ = rec (size-twf ρ₂) (s≤s (n≤m<>n (size-twf ρ₁) (size-twf ρ₂)))
                                                              in TWF-Conj (twf-thinning-sized ⊂-prf Γ'ok ρ₁ rec₁) (twf-thinning-sized ⊂-prf Γ'ok ρ₂ rec₂)
  twf-thinning-sized ⊂-prf Γ'ok (TWF-Arr argδ resδ) (acc rec) = let rec₁ = rec (size-twf argδ) (s≤s (m≤m<>n (size-twf argδ) (size-twf resδ)))
                                                                    rec₂ = rec (size-twf resδ) (s≤s (n≤m<>n (size-twf argδ) (size-twf resδ)))
                                                                    argδ' = twf-thinning-sized ⊂-prf Γ'ok argδ rec₁
                                                                    resδ' = twf-thinning-sized (PrependBoth ⊂-prf) (TCTX-Bind Γ'ok argδ') resδ rec₂
                                                                 in TWF-Arr argδ' resδ'
  twf-thinning-sized {Γ} {Γ'} ⊂-prf Γ'ok (TWF-ADT consδs) (acc rec) = let rec' = rec (size-all-cons consδs) ≤-refl
                                                                       in TWF-ADT (map-cons consδs rec')
    where
      map-cons : {cons : ADTCons n} → (α : All (Γ ⊢_) cons) → Acc _<_ (size-all-cons α) → All (Γ' ⊢_) cons
      map-cons [] _ = []
      map-cons (px ∷ pxs) (acc rec') = let rec₁ = rec' (size-twf px) (s≤s (m≤m<>n (size-twf px) (size-all-cons pxs)))
                                           rec₂ = rec' (size-all-cons pxs) (s≤s (n≤m<>n (size-twf px) (size-all-cons pxs)))
                                        in twf-thinning-sized ⊂-prf Γ'ok px rec₁ ∷ map-cons pxs rec₂

  t-thinning-sized ⊂-prf Γ'ok (T-Unit gok) _ = T-Unit Γ'ok
  t-thinning-sized ⊂-prf Γ'ok (T-Var gok x) _ = T-Var Γ'ok (⊂-preserves-∈ ⊂-prf x)
  t-thinning-sized ⊂-prf Γ'ok (T-Abs arrδ bodyδ) (acc rec) = let rec₁ = rec (size-twf arrδ) (s≤s (m≤m<>n (size-twf arrδ) (size-t bodyδ)))
                                                                 rec₂ = rec (size-t bodyδ) (s≤s (n≤m<>n (size-twf arrδ) (size-t bodyδ)))
                                                                 arrδ' = twf-thinning-sized ⊂-prf Γ'ok arrδ rec₁
                                                                 bodyδ'-ok = TCTX-Bind Γ'ok (arr-wf-dom arrδ')
                                                                 bodyδ' = t-thinning-sized (PrependBoth ⊂-prf) bodyδ'-ok bodyδ rec₂
                                                              in T-Abs arrδ' bodyδ'
  t-thinning-sized ⊂-prf Γ'ok (T-App δ₁ δ₂) (acc rec) = let rec₁ = rec (size-t δ₁) (s≤s (m≤m<>n (size-t δ₁) (size-t δ₂)))
                                                            rec₂ = rec (size-t δ₂) (s≤s (n≤m<>n (size-t δ₁) (size-t δ₂)))
                                                         in T-App (t-thinning-sized ⊂-prf Γ'ok δ₁ rec₁) (t-thinning-sized ⊂-prf Γ'ok δ₂ rec₂)
  t-thinning-sized {Γ} {Γ'} ⊂-prf Γ'ok (T-Case resδ scrut branches) (acc rec) =
    let rec₁ = rec (size-twf resδ) (s≤s (n≤m<>n<>k (size-t scrut) (size-twf resδ) (size-bs branches)))
        rec₂ = rec (size-t scrut) (s≤s (m≤m<>n<>k (size-t scrut) (size-twf resδ) (size-bs branches)))
        rec₃ = rec (size-bs branches) (s≤s (k≤m<>n<>k (size-t scrut) (size-twf resδ) (size-bs branches)))
     in T-Case (twf-thinning-sized ⊂-prf Γ'ok resδ rec₁) (t-thinning-sized ⊂-prf Γ'ok scrut rec₂) (thin-branches branches rec₃)
    where
      thin-branches : ∀ {τ cons} {bs : CaseBranches n} → (δ : BranchesHaveType Γ cons bs τ) → Acc _<_ (size-bs δ) → BranchesHaveType Γ' cons bs τ
      thin-branches NoBranches _ = NoBranches
      thin-branches (OneMoreBranch εδ rest) (acc rec') =
        let branch-Γ-ok = Γ⊢ε⦂τ-⇒-Γok εδ
            rec₁ = rec' (size-twf (Γok-head (Γ⊢ε⦂τ-⇒-Γok εδ))) (size-lemma₁ (size-bs rest) εδ)
            rec₂ = rec' (size-t εδ) (s≤s (m≤m<>n (size-t εδ) (size-bs rest)))
            rec₃ = rec' (size-bs rest) (s≤s (n≤m<>n (size-t εδ) (size-bs rest)))
            branch'-Γ-ok = TCTX-Bind Γ'ok (twf-thinning-sized ⊂-prf Γ'ok (Γok-head branch-Γ-ok) rec₁)
         in OneMoreBranch (t-thinning-sized (PrependBoth ⊂-prf) branch'-Γ-ok εδ rec₂) (thin-branches rest rec₃)
  t-thinning-sized ⊂-prf Γ'ok (T-Con conArg adtτ) (acc rec) = let rec₁ = rec (size-t conArg) (s≤s (m≤m<>n (size-t conArg) (size-twf adtτ)))
                                                                  rec₂ = rec (size-twf adtτ) (s≤s (n≤m<>n (size-t conArg) (size-twf adtτ)))
                                                               in T-Con (t-thinning-sized ⊂-prf Γ'ok conArg rec₁) (twf-thinning-sized ⊂-prf Γ'ok adtτ rec₂)
  t-thinning-sized ⊂-prf Γ'ok (T-Sub εδ <:δ) (acc rec) = let rec' = rec (size-t εδ) (s≤s (m≤m<>n (size-t εδ) (size-st <:δ)))
                                                          in T-Sub (t-thinning-sized ⊂-prf Γ'ok εδ rec') (st-thinning-sized ⊂-prf <:δ)
    where
      st-thinning-sized  : ∀ {Γ Γ'} → Γ ⊂ Γ' → (δ : Γ ⊢ τ₁ <: τ₂) → (Γ' ⊢ τ₁ <: τ₂)
      st-thinning-sized ⊂-prf (ST-Base oracle just-prf) = ST-Base oracle (Oracle.thin oracle ⊂-prf just-prf)
      st-thinning-sized ⊂-prf (ST-Arr δ₁ δ₂) = ST-Arr (st-thinning-sized ⊂-prf δ₁) (st-thinning-sized (PrependBoth ⊂-prf) δ₂)

abstract
  twf-thinning : Γ ⊂ Γ' → Γ' ok → Γ ⊢ τ     → Γ' ⊢ τ
  twf-thinning ⊂-prf Γ'ok δ = twf-thinning-sized ⊂-prf Γ'ok δ (<-wellFounded _)

  t-thinning   : Γ ⊂ Γ' → Γ' ok → Γ ⊢ ε ⦂ τ → Γ' ⊢ ε ⦂ τ
  t-thinning ⊂-prf Γ'ok δ = t-thinning-sized ⊂-prf Γ'ok δ (<-wellFounded _)

  twf-weakening : Γ ok → Γ ⊢ τ' → Γ ⊢ τ → (Γ , x ⦂ τ') ⊢ τ
  twf-weakening {Γ} Γok τ'δ τδ = twf-thinning (IgnoreHead (⊂-refl Γ)) (TCTX-Bind Γok τ'δ) τδ

  t-weakening : Γ ok → Γ ⊢ τ' → Γ ⊢ ε ⦂ τ → (Γ , x ⦂ τ') ⊢ ε ⦂ τ
  t-weakening {Γ} Γok τ'δ εδ = t-thinning (IgnoreHead (⊂-refl Γ)) (TCTX-Bind Γok τ'δ) εδ
