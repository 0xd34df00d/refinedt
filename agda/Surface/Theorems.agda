module Surface.Theorems where

open import Agda.Builtin.Equality
open import Data.Bool.Base
open import Data.List.Base using (_++_ ; [_])
open import Data.List.Membership.Propositional
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.Product renaming (_,_ to _,'_)

open import Surface.Syntax
open import Surface.Substitutions
open import Surface.Derivations
open import Surface.Derivations.WF
open import Surface.Theorems.TCTX
open import Surface.Theorems.Helpers
open import Surface.Theorems.Thinning

open import Sublist
open import Misc.ContextConcat
open import Misc.Helpers
open import Misc.SnocList

-- Exchange lemmas
exchange-Γok   : Γ ⊢ τ₂ → ∀ Δ → (Γ , x₁ ⦂ τ₁ , x₂ ⦂ τ₂ , Δ) ok → (Γ , x₂ ⦂ τ₂ , x₁ ⦂ τ₁ , Δ) ok
exchange-Γ⊢τ   : Γ ⊢ τ₂ → ∀ Δ → (Γ , x₁ ⦂ τ₁ , x₂ ⦂ τ₂ , Δ) ⊢ τ → (Γ , x₂ ⦂ τ₂ , x₁ ⦂ τ₁ , Δ) ⊢ τ
exchange-Γ⊢ε⦂τ : Γ ⊢ τ₂ → ∀ Δ → (Γ , x₁ ⦂ τ₁ , x₂ ⦂ τ₂ , Δ) ⊢ ε ⦂ τ → (Γ , x₂ ⦂ τ₂ , x₁ ⦂ τ₁ , Δ) ⊢ ε ⦂ τ

exchange-Γok no-x [] (TCTX-Bind (TCTX-Bind prevOk τδ₁) τδ₂) = TCTX-Bind (TCTX-Bind prevOk no-x) (twf-weakening prevOk no-x τδ₁)
exchange-Γok no-x ((x ,' τ) ∷ Δ) (TCTX-Bind δ τδ) = TCTX-Bind (exchange-Γok no-x Δ δ) (exchange-Γ⊢τ no-x Δ τδ)

exchange-Γ⊢τ no-x Δ (TWF-TrueRef gok) = TWF-TrueRef (exchange-Γok no-x Δ gok)
exchange-Γ⊢τ no-x Δ (TWF-Base ε₁δ ε₂δ) = TWF-Base (exchange-Γ⊢ε⦂τ no-x (_ ∷ Δ) ε₁δ) (exchange-Γ⊢ε⦂τ no-x (_ ∷ Δ) ε₂δ)
exchange-Γ⊢τ no-x Δ (TWF-Conj ρ₁δ ρ₂δ) = TWF-Conj (exchange-Γ⊢τ no-x Δ ρ₁δ) (exchange-Γ⊢τ no-x Δ ρ₂δ)
exchange-Γ⊢τ no-x Δ (TWF-Arr argδ resδ) = TWF-Arr (exchange-Γ⊢τ no-x Δ argδ) (exchange-Γ⊢τ no-x (_ ∷ Δ) resδ)
exchange-Γ⊢τ {Γ = Γ} {τ₂ = τ₂} no-x Δ (TWF-ADT consδs) = TWF-ADT (exchange-cons consδs)
  where
    exchange-cons : {cons : ADTCons n}
                  → All ((Γ , x₁ ⦂ τ₁ , x₂ ⦂ τ₂ , Δ) ⊢_) cons
                  → All ((Γ , x₂ ⦂ τ₂ , x₁ ⦂ τ₁ , Δ) ⊢_) cons
    exchange-cons [] = []
    exchange-cons (px ∷ pxs) = exchange-Γ⊢τ no-x Δ px ∷ exchange-cons pxs

exchange-Γ⊢ε⦂τ no-x Δ (T-Unit gok) = T-Unit (exchange-Γok no-x Δ gok)
exchange-Γ⊢ε⦂τ no-x Δ (T-Var gok ∈) = T-Var (exchange-Γok no-x Δ gok) (∈-swap ∈)
exchange-Γ⊢ε⦂τ no-x Δ (T-Abs arrδ bodyδ) = T-Abs (exchange-Γ⊢τ no-x Δ arrδ) (exchange-Γ⊢ε⦂τ no-x (_ ∷ Δ) bodyδ)
exchange-Γ⊢ε⦂τ no-x Δ (T-App δ₁ δ₂) = T-App (exchange-Γ⊢ε⦂τ no-x Δ δ₁) (exchange-Γ⊢ε⦂τ no-x Δ δ₂)
exchange-Γ⊢ε⦂τ {Γ = Γ} {τ₂ = τ₂} no-x Δ (T-Case resδ δ branches) = T-Case (exchange-Γ⊢τ no-x Δ resδ) (exchange-Γ⊢ε⦂τ no-x Δ δ) (exchange-branches branches)
  where
    exchange-branches : ∀ {cons} {bs : CaseBranches n}
                      → BranchesHaveType (Γ , x₁ ⦂ τ₁ , x₂ ⦂ τ₂ , Δ) cons bs τ
                      → BranchesHaveType (Γ , x₂ ⦂ τ₂ , x₁ ⦂ τ₁ , Δ) cons bs τ
    exchange-branches NoBranches = NoBranches
    exchange-branches {τ₁ = τ₁} (OneMoreBranch {x = x} {conτ = conτ} εδ bht) = OneMoreBranch (exchange-Γ⊢ε⦂τ no-x (Δ , x ⦂ conτ) εδ) (exchange-branches bht)
exchange-Γ⊢ε⦂τ no-x Δ (T-Con conArg adtτ) = T-Con (exchange-Γ⊢ε⦂τ no-x Δ conArg) (exchange-Γ⊢τ no-x Δ adtτ)
exchange-Γ⊢ε⦂τ no-x Δ (T-Sub δ superδ sub) = T-Sub (exchange-Γ⊢ε⦂τ no-x Δ δ) (exchange-Γ⊢τ no-x Δ superδ) (exchange-sub Δ sub)
  where
    exchange-sub : ∀ {Γ} Δ → (Γ , x₁ ⦂ τ₁ , x₂ ⦂ τ₂ , Δ) ⊢ τ <: τ' → (Γ , x₂ ⦂ τ₂ , x₁ ⦂ τ₁ , Δ) ⊢ τ <: τ'
    exchange-sub Δ (ST-Base oracle just-prf) = ST-Base oracle (Oracle.exchange oracle just-prf)
    exchange-sub Δ (ST-Arr δ₁ δ₂) = ST-Arr (exchange-sub Δ δ₁) (exchange-sub (_ ∷ _) δ₂)


-- Some local helpers

τ∈Γ-⇒-Γ⊢τ : Γ ok → x ⦂ τ ∈ Γ → Γ ⊢ τ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind δ τδ) (here refl) = twf-weakening δ τδ τδ
τ∈Γ-⇒-Γ⊢τ (TCTX-Bind δ τδ) (there ∈-prf) = twf-weakening δ τδ (τ∈Γ-⇒-Γ⊢τ δ ∈-prf)

-- Substitution lemmas

mutual
  sub-Γok : Γ ⊢ ε ⦂ σ
          → (Γ , x ⦂ σ , Δ) ok
          → (Γ , [ x ↦ₗ ε ] Δ) ok
  sub-Γok {Δ = []} _ (TCTX-Bind prevOk _) = prevOk
  sub-Γok {Δ = (x ,' τ) ∷ Δ} εδ (TCTX-Bind prevOk τδ) = TCTX-Bind (sub-Γok εδ prevOk) (sub-Γ⊢τ εδ τδ)

  sub-Γ⊢τ : Γ ⊢ ε ⦂ σ
          → (Γ , x ⦂ σ , Δ) ⊢ τ'
          → (Γ , [ x ↦ₗ ε ] Δ) ⊢ [ x ↦ₜ ε ] τ'
  sub-Γ⊢τ εδ (TWF-TrueRef gok) = TWF-TrueRef (sub-Γok εδ gok)
  sub-Γ⊢τ εδ (TWF-Base ε₁δ ε₂δ) = TWF-Base (sub-Γ⊢ε⦂τ εδ _ ε₁δ) (sub-Γ⊢ε⦂τ εδ _ ε₂δ)
  sub-Γ⊢τ εδ (TWF-Conj ρ₁δ ρ₂δ) = TWF-Conj (sub-Γ⊢τ εδ ρ₁δ) (sub-Γ⊢τ εδ ρ₂δ)
  sub-Γ⊢τ εδ (TWF-Arr arrδ resδ) = TWF-Arr (sub-Γ⊢τ εδ arrδ) (sub-Γ⊢τ εδ resδ)
  sub-Γ⊢τ {Γ = Γ} {ε = ε} {σ = σ} εδ (TWF-ADT consδs) = TWF-ADT (sub-cons consδs)
    where
      sub-cons : {cons : ADTCons n}
               → All (λ conτ → (Γ , x ⦂ σ , Δ) ⊢ conτ) cons
               → All (λ conτ → (Γ , [ x ↦ₗ ε ] Δ ) ⊢ conτ) ([ x ↦ₐ ε ] cons)
      sub-cons [] = []
      sub-cons (px ∷ pxs) = sub-Γ⊢τ εδ px ∷ sub-cons pxs

  sub-Γ⊢ε⦂τ : Γ ⊢ ε ⦂ σ
            → (ε' : _)
            → (Γ , x ⦂ σ , Δ) ⊢ ε' ⦂ τ'
            → (Γ , [ x ↦ₗ ε ] Δ) ⊢ [ x ↦ₑ ε ] ε' ⦂ [ x ↦ₜ ε ] τ'
  sub-Γ⊢ε⦂τ εδ _  (T-Unit gok) = T-Unit (sub-Γok εδ gok)
  sub-Γ⊢ε⦂τ {x = x} εδ (SVar x') (T-Var gok ∈) with var-eq x x'
  ... | false = {! T-Var !}
  ... | true = {! !}
  sub-Γ⊢ε⦂τ εδ _  (T-Abs arrδ bodyδ) = {! !}
  sub-Γ⊢ε⦂τ εδ ε' (T-App δ₁ δ₂) = {! !}
  sub-Γ⊢ε⦂τ εδ _  (T-Case resδ δ branches) = {! !}
  sub-Γ⊢ε⦂τ εδ _  (T-Con δ adtτ) = {! !}
  sub-Γ⊢ε⦂τ εδ _  (T-Sub δ x x₁) = {! !}


Γ⊢ε⦂τ-⇒-Γ⊢τ : Γ ⊢ ε ⦂ τ → Γ ⊢ τ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Unit gok) = TWF-TrueRef gok
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Var gok ∈-prf) = τ∈Γ-⇒-Γ⊢τ gok ∈-prf
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Abs arrδ _) = arrδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-App δ₁ δ₂) = sub-Γ⊢τ δ₂ (arr-wf-⇒-cod-wf (Γ⊢ε⦂τ-⇒-Γ⊢τ δ₁))
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Case resδ _ _) = resδ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Con _ adtτ) = adtτ
Γ⊢ε⦂τ-⇒-Γ⊢τ (T-Sub δ superδ sub) = superδ
