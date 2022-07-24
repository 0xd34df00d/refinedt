{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Subtyping where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Vec as V using (lookup; _∷_; []; zip; zipWith)
open import Data.Vec.Relation.Unary.All as VA using (All; _∷_; []; tabulate)

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Derivations.Algorithmic

<:-reflexive : Γ ⊢[ θ ] τ <: τ
<:-reflexive {θ = θ} {τ = ⟨ _ ∣ _ ⟩} = ST-Base (Oracle.<:-refl θ _ _ _)
<:-reflexive {τ = _ ⇒ _} = ST-Arr <:-reflexive <:-reflexive
<:-reflexive {τ = ⊍ cons} = ST-ADT (go cons)
  where
  go : (cons : ADTCons nₐ ℓ) → AllSubtypes Γ θ cons cons
  go [] = []
  go (con ∷ cons) = <:-reflexive ∷ go cons

as-sub : ∃[ κ ] (Γ ⊢[ θ , φ of κ ] ε ⦂ τ)
       → Γ ⊢[ θ , φ of t-sub ] ε ⦂ τ
as-sub ⟨ t-sub , εδ ⟩ = εδ
as-sub ⟨ not-t-sub , εδ ⟩ = T-Sub εδ <:-reflexive

Γ⊢τ'<:τ-⇒-Γ⊢τ₀⇒τ'<:τ₀⇒τ : Γ , τ₀ ⊢[ θ ] τ' <: τ
                        → Γ ⊢[ θ ] τ₀ ⇒ τ' <: τ₀ ⇒ τ
Γ⊢τ'<:τ-⇒-Γ⊢τ₀⇒τ'<:τ₀⇒τ τ'<:τ = ST-Arr <:-reflexive τ'<:τ

private module M {σ σ' : SType ℓ} {Γ : Ctx ℓ} (σ-<:δ : Γ ⊢[ θ ] σ' <: σ) where
  <:-narrowing : (Δ : CtxSuffix (suc ℓ) k)
               → Γ , σ  ++ Δ ⊢[ θ ] τ₂' <: τ₂
               → Γ , σ' ++ Δ ⊢[ θ ] τ₂' <: τ₂
  <:-narrowing Δ (ST-Base is-just) = ST-Base (Oracle.narrowing θ {- TODO σ-<:δ -} is-just)
  <:-narrowing Δ (ST-Arr <:₁δ <:₂δ)
    = let <:₁δ' = <:-narrowing Δ <:₁δ
       in ST-Arr
            <:₁δ'
            (<:-narrowing (Δ , _) <:₂δ)
  <:-narrowing {k = k} Δ (ST-ADT cons-<:) = ST-ADT (go cons-<:)
    where
    go : {cons' cons : ADTCons nₐ (k + suc ℓ)}
       → AllSubtypes (Γ , σ  ++ Δ) θ cons' cons
       → AllSubtypes (Γ , σ' ++ Δ) θ cons' cons
    go {cons' = []}    {[]}    []              = []
    go {cons' = _ ∷ _} {_ ∷ _} (<:δ ∷ cons-<:) = <:-narrowing Δ <:δ ∷ go cons-<:

open M public

<:-transitive : ∀ {τ''}
              → Γ ⊢[ θ ] τ'' <: τ'
              → Γ ⊢[ θ ] τ'  <: τ
              → Γ ⊢[ θ ] τ'' <: τ
<:-transitive {θ = θ} (ST-Base is-just') (ST-Base is-just) = ST-Base (Oracle.trans θ is-just' is-just)
<:-transitive (ST-Arr <:₁'δ <:₂'δ) (ST-Arr <:₁δ <:₂δ)
  = ST-Arr
      (<:-transitive <:₁δ <:₁'δ)
      (<:-transitive (<:-narrowing <:₁δ ⊘ <:₂'δ) <:₂δ)
<:-transitive (ST-ADT cons-<:₁) (ST-ADT cons-<:₂) = ST-ADT (go cons-<:₁ cons-<:₂)
  where
  go : {cons'' cons' cons : ADTCons nₐ ℓ}
     → AllSubtypes Γ θ cons'' cons'
     → AllSubtypes Γ θ cons'  cons
     → AllSubtypes Γ θ cons'' cons
  go {cons'' = []}    {[]}    {[]}    []                []                = []
  go {cons'' = _ ∷ _} {_ ∷ _} {_ ∷ _} (<:δ₁ ∷ cons-<:₁) (<:δ₂ ∷ cons-<:₂) = <:-transitive <:δ₁ <:δ₂ ∷ go cons-<:₁ cons-<:₂

trans-sub : Γ ⊢[ θ ] τ' <: τ
          → Γ ⊢[ θ , φ of t-sub ] ε ⦂ τ'
          → Γ ⊢[ θ , φ of t-sub ] ε ⦂ τ
trans-sub <:δ (T-Sub εδ <:'δ) = T-Sub εδ (<:-transitive <:'δ <:δ)

as-sub' : Γ ⊢[ θ ] τ' <: τ
        → ∃[ κ ] (Γ ⊢[ θ , φ of κ ] ε ⦂ τ')
        → Γ ⊢[ θ , φ of t-sub ] ε ⦂ τ
as-sub' <:δ ⟨ t-sub , εδ ⟩ = trans-sub <:δ εδ
as-sub' <:δ ⟨ not-t-sub , εδ ⟩ = T-Sub εδ <:δ
