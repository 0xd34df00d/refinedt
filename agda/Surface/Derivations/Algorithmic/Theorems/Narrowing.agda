module Surface.Derivations.Algorithmic.Theorems.Narrowing where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
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

<:-transitive : ∀ {τ''}
              → Γ ⊢[ θ , φ ] τ'' <: τ'
              → Γ ⊢[ θ , φ ] τ'  <: τ
              → Γ ⊢[ θ , φ ] τ'' <: τ

as-sub' : Γ ⊢[ θ , φ ] τ' <: τ
        → ∃[ κ ] (Γ ⊢[ θ , φ of κ ] ε ⦂ τ')
        → Γ ⊢[ θ , φ of t-sub ] ε ⦂ τ
as-sub' <:δ ⟨ t-sub , T-Sub εδ τδ <:'δ ⟩ = T-Sub εδ {! Γ⊢τ'<:τ-⇒-Γ⊢τ <:δ !} (<:-transitive <:'δ <:δ)
as-sub' <:δ ⟨ not-t-sub , εδ ⟩ = T-Sub εδ {! Γ⊢τ'<:τ-⇒-Γ⊢τ <:δ !} <:δ

module M {σ : SType ℓ} (σ-<:δ : Γ ⊢[ θ , φ ] σ' <: σ) (Γ⊢σ' : Γ ⊢[ θ , φ ] σ') where mutual
  <:-narrowing : ∀ Δ
               → Γ , σ  ++ Δ ⊢[ θ , φ ] τ₂ <: τ₂'
               → Γ , σ' ++ Δ ⊢[ θ , φ ] τ₂ <: τ₂'
  <:-narrowing Δ <:δ = {! !}

  Γok-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                → (Γ , σ  ++ Δ) ok[ θ , φ ]
                → (Γ , σ' ++ Δ) ok[ θ , φ ]
  Γok-narrowing Δ Γδ = {! Γδ !}

  Γ⊢τ-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                → Γ , σ  ++ Δ ⊢[ θ , φ ] τ
                → Γ , σ' ++ Δ ⊢[ θ , φ ] τ
  Γ⊢τ-narrowing Δ (TWF-TrueRef Γok) = TWF-TrueRef (Γok-narrowing Δ Γok)
  Γ⊢τ-narrowing Δ (TWF-Base ε₁δ ε₂δ)
    = let ε₁δ' = as-sub (Γ⊢ε⦂τ-narrowing (Δ , _) ε₁δ)
          ε₂δ' = as-sub (Γ⊢ε⦂τ-narrowing (Δ , _) ε₂δ)
       in TWF-Base ε₁δ' ε₂δ'
  Γ⊢τ-narrowing Δ (TWF-Conj τδ τδ₁) = {! !}
  Γ⊢τ-narrowing Δ (TWF-Arr τδ τδ₁) = {! !}
  Γ⊢τ-narrowing Δ (TWF-ADT consδs) = {! !}

  SVar-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                 → (Γ , σ ++ Δ) ok[ θ , φ ]
                 → τ ∈ Γ , σ ++ Δ at ι
                 → ∃[ κ ] (Γ , σ' ++ Δ ⊢[ θ , φ of κ ] SVar ι ⦂ τ)
  SVar-narrowing ⊘ (TCTX-Bind Γok τδ) (∈-zero refl)
    = ⟨ _ , T-Sub (T-Var (TCTX-Bind Γok Γ⊢σ') (∈-zero refl)) (Γ⊢τ-weakening Γok Γ⊢σ' τδ) (<:-weakening Γok Γ⊢σ' σ-<:δ) ⟩
  SVar-narrowing ⊘ (TCTX-Bind Γok τδ) (∈-suc refl ∈) = ⟨ _ , T-Var (TCTX-Bind Γok Γ⊢σ') (∈-suc refl ∈) ⟩
  SVar-narrowing (Δ , τ) Γ,σ,Δ-ok (∈-zero refl) = ⟨ _ , T-Var (Γok-narrowing (Δ , _) Γ,σ,Δ-ok) (∈-zero refl) ⟩
  SVar-narrowing (Δ , τ) (TCTX-Bind Γ,σ,Δ-ok Γ,σ,Δ⊢τ) (∈-suc refl ∈)
    with ⟨ _ , εδ ⟩ ← SVar-narrowing Δ Γ,σ,Δ-ok ∈
       = ⟨ _ , Γ⊢ε⦂τ-weakening (Γok-narrowing Δ Γ,σ,Δ-ok) (Γ⊢τ-narrowing Δ Γ,σ,Δ⊢τ) εδ ⟩

  Γ⊢ε⦂τ-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                  → Γ , σ  ++ Δ ⊢[ θ , φ of κ ] ε ⦂ τ
                  → ∃[ κ' ] (Γ , σ' ++ Δ ⊢[ θ , φ of κ' ] ε ⦂ τ)
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
  ... | ⟨ t-sub , T-Sub ε₁δ' τ₁⇒τ₂δ <:δ@(ST-Arr <:₁δ _ _ _) ⟩
         = ⟨ _
           , T-Sub
              (T-App ε₁δ' (as-sub' <:₁δ (Γ⊢ε⦂τ-narrowing Δ ε₂δ)) refl {! !})
              (Γ⊢τ-narrowing Δ resτδ)
              {! !}
           ⟩
  ... | ⟨ not-t-sub , ε₁δ' ⟩ = ⟨ _ , T-App ε₁δ' (as-sub (Γ⊢ε⦂τ-narrowing Δ ε₂δ)) refl (Γ⊢τ-narrowing Δ resτδ) ⟩
  Γ⊢ε⦂τ-narrowing Δ (T-Case resδ εδ branches-well-typed) = {! !}
  Γ⊢ε⦂τ-narrowing Δ (T-Con ≡-prf εδ adtτ) = {! !}
  Γ⊢ε⦂τ-narrowing Δ (T-Sub εδ τδ <:δ) = {! !}

open M public

<:-transitive {θ = θ} (ST-Base is-just' ρ₁δ _) (ST-Base is-just _ ρ₃δ) = ST-Base (Oracle.trans θ is-just' is-just) ρ₁δ ρ₃δ
<:-transitive (ST-Arr <:₁'δ <:₂'δ₁ τ₁⇒τ₂'δ _) (ST-Arr <:₁δ <:₂δ _ τ₁'⇒τ₂δ)
  = ST-Arr
      (<:-transitive <:₁δ <:₁'δ)
      (<:-transitive (<:-narrowing <:₁δ {! !} ⊘ <:₂'δ₁) <:₂δ)
      τ₁⇒τ₂'δ
      τ₁'⇒τ₂δ
<:-transitive (ST-ADT ⊍δ) (ST-ADT _) = ST-ADT ⊍δ
