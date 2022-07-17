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

as-sub' : Γ ⊢[ θ ] τ' <: τ
        → Γ ⊢[ θ , φ ] τ
        → ∃[ κ ] (Γ ⊢[ θ , φ of κ ] ε ⦂ τ')
        → Γ ⊢[ θ , φ of t-sub ] ε ⦂ τ
as-sub' <:δ τδ ⟨ t-sub , T-Sub εδ _ <:'δ ⟩ = T-Sub εδ τδ (<:-transitive <:'δ <:δ)
as-sub' <:δ τδ ⟨ not-t-sub , εδ ⟩ = T-Sub εδ τδ <:δ

module M {σ : SType ℓ} (σ-<:δ : Γ ⊢[ θ ] σ' <: σ) (Γ⊢σ' : Γ ⊢[ θ , M ] σ') where mutual
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
  Γ⊢τ-narrowing Δ (TWF-Conj τ₁δ τ₂δ) = TWF-Conj (Γ⊢τ-narrowing Δ τ₁δ) (Γ⊢τ-narrowing Δ τ₂δ)
  Γ⊢τ-narrowing Δ (TWF-Arr τ₁δ τ₂δ) = TWF-Arr (Γ⊢τ-narrowing Δ τ₁δ) (Γ⊢τ-narrowing (Δ , _) τ₂δ)
  Γ⊢τ-narrowing Δ (TWF-ADT consδs) = TWF-ADT (cons-narrowing Δ consδs)

  cons-narrowing : {cons : ADTCons nₐ (k + suc ℓ)}
                 → (Δ : CtxSuffix (suc ℓ) k)
                 → All ((Γ , σ  ++ Δ) ⊢[ θ , M ]_) cons
                 → All ((Γ , σ' ++ Δ) ⊢[ θ , M ]_) cons
  cons-narrowing Δ [] = []
  cons-narrowing Δ (τδ ∷ δs) = Γ⊢τ-narrowing Δ τδ ∷ cons-narrowing Δ δs

  SVar-narrowing : (Δ : CtxSuffix (suc ℓ) k)
                 → (Γ , σ ++ Δ) ok[ θ , M ]
                 → τ ∈ Γ , σ ++ Δ at ι
                 → ∃[ κ ] (Γ , σ' ++ Δ ⊢[ θ , M of κ ] SVar ι ⦂ τ)
  SVar-narrowing ⊘ (TCTX-Bind Γok τδ) (∈-zero refl)
    = ⟨ _ , T-Sub (T-Var (TCTX-Bind Γok Γ⊢σ') (∈-zero refl)) (Γ⊢τ-weakening Γok Γ⊢σ' τδ) (<:-weakening σ-<:δ) ⟩
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
              (Γ⊢τ'<:τ-⇒-Γ⊢τ₀⇒τ'<:τ₀⇒τ <:δ)
          ⟩
  ... | ⟨ not-t-sub , εδ' ⟩ = ⟨ _ , T-Abs (Γ⊢τ-narrowing Δ arrδ) εδ' ⟩
  Γ⊢ε⦂τ-narrowing Δ (T-App ε₁δ ε₂δ refl resτδ) with Γ⊢ε⦂τ-narrowing Δ ε₁δ
  ... | ⟨ not-t-sub , ε₁δ' ⟩ = ⟨ _ , T-App ε₁δ' (as-sub (Γ⊢ε⦂τ-narrowing Δ ε₂δ)) refl (Γ⊢τ-narrowing Δ resτδ) ⟩
  ... | ⟨ t-sub , T-Sub ε₁δ' τ₁⇒τ₂δ (ST-Arr <:₁δ <:₂δ) ⟩
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
