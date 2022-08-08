module Surface.Derivations.Algorithmic.Theorems.Subtyping.Enriched where

open import Data.Fin using (raise; zero; suc)
open import Data.Nat using (zero; suc)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Vec as V using (lookup; _∷_; []; zip; zipWith)
open import Data.Vec.Relation.Unary.All as VA using (All; _∷_; []; tabulate)
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Surface.Syntax
open import Surface.Syntax.CtxSuffix
open import Surface.Derivations.Algorithmic
open import Surface.Derivations.Algorithmic.Theorems.Agreement.TypeWellFormedness.Enriched

<:-reflexive : Γ ⊢[ θ , E ] τ
             → Γ ⊢[ θ , E ] τ <: τ
<:-reflexive {θ = θ} {τ = ⟨ _ ∣ _ ⟩} τδ = ST-Base (Oracle.<:-refl θ _ _ _) ⦃ enriched τδ ⦄ ⦃ enriched τδ ⦄
<:-reflexive {τ = _ ⇒ _} τδ@(TWF-Arr τ₁δ τ₂δ)
  = ST-Arr
      (<:-reflexive τ₁δ)
      (<:-reflexive τ₂δ)
      ⦃ enriched τδ ⦄
      ⦃ enriched τδ ⦄
<:-reflexive {τ = ⊍ _} (TWF-ADT consδs) = ST-ADT (go consδs)
  where
  go : {cons : ADTCons nₐ ℓ}
     → (consδs : All (Γ ⊢[ θ , E ]_) cons)
     → AllSubtypes Γ θ E cons cons
  go [] = []
  go (τδ ∷ consδs) = <:-reflexive τδ ∷ go consδs

as-sub : Γ ⊢[ θ , E of κ ] ε ⦂ τ
       → Γ ⊢[ θ , E of t-sub ] ε ⦂ τ
as-sub {κ = t-sub} εδ = εδ
as-sub {κ = not-t-sub} εδ
  = let τδ = Γ⊢ε⦂τ-⇒-Γ⊢τ εδ
     in T-Sub εδ (<:-reflexive τδ) ⦃ enriched τδ ⦄
