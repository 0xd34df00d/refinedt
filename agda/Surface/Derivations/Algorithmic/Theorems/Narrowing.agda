module Surface.Derivations.Algorithmic.Theorems.Narrowing where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Syntax.Membership
open import Surface.Syntax.Substitution
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Agreement
open import Surface.Derivations.Algorithmic.Theorems.Helpers
open import Surface.Derivations.Algorithmic.Theorems.Subtyping
open import Surface.Derivations.Algorithmic.Theorems.Thinning

<:-narrowing : {σ σ' : SType ℓ} {Γ : Ctx ℓ}
             → (σ-<:δ : Γ ⊢[ θ , M ] σ' <: σ)
             → (Δ : CtxSuffix (suc ℓ) k)
             → Γ , σ  ++ Δ ⊢[ θ , M ] τ₂' <: τ₂
             → Γ , σ' ++ Δ ⊢[ θ , M ] τ₂' <: τ₂
<:-narrowing {θ = θ} σ-<:δ Δ (ST-Base is-just _ _)
  = ST-Base (Oracle.narrowing θ {- TODO σ-<:δ -} is-just) omitted omitted
<:-narrowing σ-<:δ Δ (ST-Arr <:₁δ <:₂δ _ _)
  = let <:₁δ' = <:-narrowing σ-<:δ Δ <:₁δ
     in ST-Arr
          <:₁δ'
          (<:-narrowing σ-<:δ (Δ , _) <:₂δ)
          omitted
          omitted
<:-narrowing σ-<:δ Δ (ST-ADT _) = ST-ADT omitted

<:-transitive : ∀ {τ''}
              → Γ ⊢[ θ , M ] τ'' <: τ'
              → Γ ⊢[ θ , M ] τ'  <: τ
              → Γ ⊢[ θ , M ] τ'' <: τ
<:-transitive {θ = θ} (ST-Base is-just' _ _) (ST-Base is-just _ _) = ST-Base (Oracle.trans θ is-just' is-just) omitted omitted
<:-transitive (ST-Arr <:₁'δ <:₂'δ _ _) (ST-Arr <:₁δ <:₂δ _ _)
  = ST-Arr
      (<:-transitive <:₁δ <:₁'δ)
      (<:-transitive (<:-narrowing <:₁δ ⊘ <:₂'δ) <:₂δ)
      omitted
      omitted
<:-transitive (ST-ADT ⊍δ) (ST-ADT _) = ST-ADT omitted

as-sub' : Γ ⊢[ θ , M ] τ' <: τ
        → Γ ⊢[ θ , M ] τ
        → ∃[ κ ] (Γ ⊢[ θ , M of κ ] ε ⦂ τ')
        → Γ ⊢[ θ , M of t-sub ] ε ⦂ τ
as-sub' <:δ τδ ⟨ t-sub , T-Sub εδ _ <:'δ ⟩ = T-Sub εδ τδ (<:-transitive <:'δ <:δ)
as-sub' <:δ τδ ⟨ not-t-sub , εδ ⟩ = T-Sub εδ τδ <:δ

module M {σ : SType ℓ} (σ-<:δ : Γ ⊢[ θ , M ] σ' <: σ) (Γ⊢σ' : Γ ⊢[ θ , M ] σ') where mutual
  Γok-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                → (Γ , σ  ++ Δ) ok[ θ , M ]
                → (Γ , σ' ++ Δ) ok[ θ , M ]
  Γok-narrowing ⊘ (TCTX-Bind Γok τδ) = TCTX-Bind Γok Γ⊢σ'
  Γok-narrowing (Δ , _) (TCTX-Bind Γ,σ,Δ-ok τδ) = TCTX-Bind (Γok-narrowing Δ Γ,σ,Δ-ok) (Γ⊢τ-narrowing Δ τδ)

  Γ⊢τ-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                → Γ , σ  ++ Δ ⊢[ θ , M ] τ
                → Γ , σ' ++ Δ ⊢[ θ , M ] τ
  Γ⊢τ-narrowing Δ (TWF-TrueRef Γok) = TWF-TrueRef (Γok-narrowing Δ Γok)
  Γ⊢τ-narrowing Δ (TWF-Base ε₁δ ε₂δ)
    = let ε₁δ' = as-sub (Γ⊢ε⦂τ-narrowing (Δ , _) ε₁δ)
          ε₂δ' = as-sub (Γ⊢ε⦂τ-narrowing (Δ , _) ε₂δ)
       in TWF-Base ε₁δ' ε₂δ'
  Γ⊢τ-narrowing Δ (TWF-Conj τ₁δ τ₂δ) = {! !}
  Γ⊢τ-narrowing Δ (TWF-Arr τ₁δ τ₂δ) = {! !}
  Γ⊢τ-narrowing Δ (TWF-ADT consδs) = {! !}

  SVar-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                 → (Γ , σ ++ Δ) ok[ θ , M ]
                 → τ ∈ Γ , σ ++ Δ at ι
                 → ∃[ κ ] (Γ , σ' ++ Δ ⊢[ θ , M of κ ] SVar ι ⦂ τ)
  SVar-narrowing ⊘ (TCTX-Bind Γok τδ) (∈-zero refl)
    = ⟨ _ , T-Sub (T-Var (TCTX-Bind Γok Γ⊢σ') (∈-zero refl)) (Γ⊢τ-weakening Γok Γ⊢σ' τδ) (<:-weakening Γok Γ⊢σ' σ-<:δ) ⟩
  SVar-narrowing ⊘ (TCTX-Bind Γok τδ) (∈-suc refl ∈) = ⟨ _ , T-Var (TCTX-Bind Γok Γ⊢σ') (∈-suc refl ∈) ⟩
  SVar-narrowing (Δ , τ) Γ,σ,Δ-ok (∈-zero refl) = ⟨ _ , T-Var (Γok-narrowing (Δ , _) Γ,σ,Δ-ok) (∈-zero refl) ⟩
  SVar-narrowing (Δ , τ) (TCTX-Bind Γ,σ,Δ-ok Γ,σ,Δ⊢τ) (∈-suc refl ∈)
    with ⟨ _ , εδ ⟩ ← SVar-narrowing Δ Γ,σ,Δ-ok ∈
       = ⟨ _ , Γ⊢ε⦂τ-weakening (Γok-narrowing Δ Γ,σ,Δ-ok) (Γ⊢τ-narrowing Δ Γ,σ,Δ⊢τ) εδ ⟩

  Γ⊢ε⦂τ-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                  → Γ , σ  ++ Δ ⊢[ θ , M of κ ] ε ⦂ τ
                  → ∃[ κ' ] (Γ , σ' ++ Δ ⊢[ θ , M of κ' ] ε ⦂ τ)
  Γ⊢ε⦂τ-narrowing Δ (T-Unit Γok) = ⟨ _ , T-Unit (Γok-narrowing Δ Γok) ⟩
  Γ⊢ε⦂τ-narrowing Δ (T-Var Γok ∈) = SVar-narrowing Δ Γok ∈
  Γ⊢ε⦂τ-narrowing Δ (T-Abs arrδ εδ) with Γ⊢ε⦂τ-narrowing (Δ , _) εδ
  ... | ⟨ t-sub , T-Sub εδ' τδ <:δ ⟩
        = ⟨ _
          , T-Sub
              (T-Abs (Γ,τ₁⊢τ₂-⇒-Γ⊢τ₁⇒τ₂ (Γ⊢ε⦂τ-⇒-Γ⊢τ εδ')) εδ')
              (Γ⊢τ-narrowing Δ arrδ)
              (Γ⊢τ'<:τ-⇒-Γ⊢τ₀⇒τ'<:τ₀⇒τ (Γok-head (Γ⊢τ-⇒-Γok τδ)) <:δ)
          ⟩
  ... | ⟨ not-t-sub , εδ' ⟩ = ⟨ _ , T-Abs (Γ⊢τ-narrowing Δ arrδ) εδ' ⟩
  Γ⊢ε⦂τ-narrowing Δ (T-App ε₁δ ε₂δ refl resτδ) with Γ⊢ε⦂τ-narrowing Δ ε₁δ
  ... | ⟨ not-t-sub , ε₁δ' ⟩ = ⟨ _ , T-App ε₁δ' (as-sub (Γ⊢ε⦂τ-narrowing Δ ε₂δ)) refl (Γ⊢τ-narrowing Δ resτδ) ⟩
  ... | ⟨ t-sub , T-Sub ε₁δ' τ₁⇒τ₂δ (ST-Arr <:₁δ <:₂δ _ _) ⟩
        = let τ₁δ' = case Γ⊢ε⦂τ-⇒-Γ⊢τ ε₁δ' of λ { (TWF-Arr τ₁δ' _) → τ₁δ' }
              ε₂δ' = as-sub' <:₁δ τ₁δ' (Γ⊢ε⦂τ-narrowing Δ ε₂δ)
           in ⟨ _
              , T-Sub
                 (T-App ε₁δ' ε₂δ' refl {! !})
                 (Γ⊢τ-narrowing Δ resτδ)
                 {! !}
              ⟩
  Γ⊢ε⦂τ-narrowing Δ (T-Case resδ εδ branches-well-typed) = {! !}
  Γ⊢ε⦂τ-narrowing Δ (T-Con ≡-prf εδ adtτ) = {! !}
  Γ⊢ε⦂τ-narrowing Δ (T-Sub εδ τδ <:δ) with Γ⊢ε⦂τ-narrowing Δ εδ
  ... | ⟨ t-sub , T-Sub εδ' τ'δ <:'δ ⟩ = ⟨ _ , T-Sub εδ' (Γ⊢τ-narrowing Δ τδ) (<:-transitive <:'δ (<:-narrowing σ-<:δ Δ <:δ)) ⟩
  ... | ⟨ not-t-sub , εδ' ⟩ = ⟨ _ , T-Sub εδ' (Γ⊢τ-narrowing Δ τδ) (<:-narrowing σ-<:δ Δ <:δ) ⟩
