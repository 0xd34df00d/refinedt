{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.Theorems.Subtyping where

open import Data.Fin using (raise; zero; suc)
open import Data.Nat using (zero; suc)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Vec as V using (lookup; _∷_; []; zip; zipWith)
open import Data.Vec.Relation.Unary.All as VA using (All; _∷_; []; tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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


open import Common.Helpers
open import Surface.Syntax.Renaming as R
open import Surface.Syntax.Substitution as S

private module N {Γ : Ctx ℓ} (εδ : Γ ⊢[ θ , φ of t-sub ] ε ⦂ σ) where
  sub-Γ⊢τ'<:τ : (Δ : ,-CtxSuffix ℓ σ k)
              → Γ ,σ, Δ ⊢[ θ ] τ' <: τ
              → Γ ++ [↦Δ ε ] Δ ⊢[ θ ] [ ℓ ↦τ< ε ] τ' <: [ ℓ ↦τ< ε ] τ
  sub-Γ⊢τ'<:τ Δ (ST-Base is-just) = ST-Base (Oracle.subst {- TODO εδ -} θ is-just)
  sub-Γ⊢τ'<:τ {k = k} Δ (ST-Arr {τ₂' = τ₂'} {τ₂ = τ₂} <:₁δ <:₂δ)
    rewrite S.act-τ-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) τ₂
          | S.act-τ-extensionality (S.ext-replace-comm (R.weaken-ε-k k ε) (ctx-idx k)) τ₂'
          | R.act-ε-distr (raise k) suc ε
          = ST-Arr (sub-Γ⊢τ'<:τ Δ <:₁δ) (sub-Γ⊢τ'<:τ (Δ , _) <:₂δ)
  sub-Γ⊢τ'<:τ {k = k} Δ (ST-ADT cons-<:) = ST-ADT (go cons-<:)
    where
    go : {cons' cons : ADTCons nₐ (suc k + ℓ)}
       → AllSubtypes (Γ ,σ, Δ) θ cons' cons
       → AllSubtypes (Γ ++ [↦Δ ε ] Δ) θ ([ ℓ ↦c< ε ] cons') ([ ℓ ↦c< ε ] cons)
    go {cons' = []}    {[]}    []              = []
    go {cons' = _ ∷ _} {_ ∷ _} (<:δ ∷ cons-<:) = sub-Γ⊢τ'<:τ Δ <:δ ∷ go cons-<:

open N public

sub-Γ⊢τ'<:τ-front : (εδ : Γ ⊢[ θ , φ of t-sub ] ε ⦂ σ)
                  → Γ , σ ⊢[ θ ] τ' <: τ
                  → Γ ⊢[ θ ] [ zero ↦τ ε ] τ' <: [ zero ↦τ ε ] τ
sub-Γ⊢τ'<:τ-front {ε = ε} εδ <:δ
  with <:δ' ← sub-Γ⊢τ'<:τ εδ [ _ ] <:δ
  rewrite R.act-ε-id (λ _ → refl) ε
        = <:δ'
