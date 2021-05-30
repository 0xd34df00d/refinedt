{-# OPTIONS --safe #-}

module Core.Syntax.Derived.Typing where

open import Data.Fin using (zero; suc)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Core.Syntax
open import Core.Syntax.Derived
open import Core.Syntax.Membership
open import Core.Syntax.Renaming as R
open import Core.Syntax.Renaming.Distributivity as R
open import Core.Syntax.Substitution as S
open import Core.Syntax.Substitution.Stable
open import Core.Derivations
open import Core.Operational
open import Core.Operational.BetaEquivalence

head-well-formed : Γ , τ ⊢ ε ⦂ τ'
                 → ∃[ s ] (Γ ⊢ τ ⦂ CSort s)
head-well-formed (CT-Var δ) = ⟨ _ , δ ⟩
head-well-formed (CT-Weaken _ δ) = ⟨ _ , δ ⟩
head-well-formed (CT-Form δ _) = head-well-formed δ
head-well-formed (CT-App _ δ) = head-well-formed δ
head-well-formed (CT-Abs _ δ) = head-well-formed δ
head-well-formed (CT-Conv _ δ _) = head-well-formed δ
head-well-formed (CT-UnitType δ) = head-well-formed δ
head-well-formed (CT-UnitTerm δ) = head-well-formed δ
head-well-formed (CT-ADTForm (δ ∷ _)) = head-well-formed δ
head-well-formed (CT-ADTCon _ _ δ) = head-well-formed δ
head-well-formed (CT-ADTCase _ δ _) = head-well-formed δ

τ∈Γ-wf : Γ ⊢ τ' ⦂ CSort s'
       → τ ∈ Γ at ι
       → ∃[ s ] (Γ ⊢ τ ⦂ CSort s)
τ∈Γ-wf δ (∈-zero refl) with head-well-formed δ
... | ⟨ s , δ' ⟩ = ⟨ s , CT-Weaken δ' δ' ⟩
τ∈Γ-wf δ (∈-suc refl ∈) with head-well-formed δ
... | ⟨ s' , δ' ⟩ with τ∈Γ-wf δ' ∈
...   | ⟨ s , δ₀ ⟩ = ⟨ s , CT-Weaken δ₀ δ' ⟩

CT-VarW : Γ ⊢ τ ⦂ CSort s
        → τ ∈ Γ at ι
        → Γ ⊢ CVar ι ⦂ τ
CT-VarW δ (∈-zero refl) with head-well-formed δ
... | ⟨ _ , δ' ⟩ = CT-Var δ'
CT-VarW δ (∈-suc refl ∈) with head-well-formed δ
... | ⟨ _ , δ' ⟩ with τ∈Γ-wf δ' ∈
...   | ⟨ _ , δ'' ⟩ = CT-Weaken (CT-VarW δ'' ∈) δ'

⇒'-well-typed : Γ ⊢ τ₁ ⦂ CSort s₁
              → Γ ⊢ τ₂ ⦂ CSort s₂
              → Γ ⊢ (τ₁ ⇒' τ₂) ⦂ CSort s₂
⇒'-well-typed τ₁δ τ₂δ = CT-Form τ₁δ (CT-Weaken τ₂δ τ₁δ)

Γ⊢⋆⦂□ : Γ ⊢ ε ⦂ τ
      → Γ ⊢ ⋆ₑ ⦂ □ₑ
Γ⊢⋆⦂□ {Γ = ⊘} _ = CT-Sort
Γ⊢⋆⦂□ {Γ = Γ , τ} δ with head-well-formed δ
... | ⟨ _ , δ' ⟩ = CT-Weaken (Γ⊢⋆⦂□ δ') δ'

Σ-cont-well-typed : ∀ {Γ : Ctx ℓ} {P}
                  → Γ ⊢ τ ⦂ CSort s
                  → Γ ⊢ P ⦂ τ ⇒' ⋆ₑ
                  → Γ , ⋆ₑ ⊢ Σ-cont τ P ⦂ ⋆ₑ
Σ-cont-well-typed δτ δP =
  let Γ,⋆⊢τ = CT-Weaken δτ (Γ⊢⋆⦂□ δτ)
   in CT-Form
        Γ,⋆⊢τ
        (⇒'-well-typed
          (CT-App
            (CT-Weaken
              (CT-Weaken δP (Γ⊢⋆⦂□ δτ))
              Γ,⋆⊢τ
            )
            (CT-Var Γ,⋆⊢τ)
          )
          (CT-Weaken (CT-Var (Γ⊢⋆⦂□ δτ)) Γ,⋆⊢τ)
        )

Σ-well-typed : ∀ {Γ : Ctx ℓ} {P}
             → Γ ⊢ τ ⦂ CSort s
             → Γ ⊢ P ⦂ τ ⇒' ⋆ₑ
             → Γ ⊢ Σ[ τ ] P ⦂ ⋆ₑ
Σ-well-typed δτ δP =
  CT-Form
    (Γ⊢⋆⦂□ δτ)
    (CT-Form
      (Σ-cont-well-typed δτ δP)
      (CT-Weaken (CT-Var (Γ⊢⋆⦂□ δτ)) (Σ-cont-well-typed δτ δP))
    )

ext-suc-suc-is-suc² : (ε : CExpr ℓ)
                    → R.act-ε (R.ext suc) (weaken-ε ε) ≡ weaken-ε-k 2 ε
ext-suc-suc-is-suc² ε
  rewrite R.act-ε-distr suc (R.ext suc) ε
        | R.act-ε-distr suc suc ε
        = refl

Σ-ctor-well-typed : ∀ {Γ : Ctx ℓ} {P} {π}
                  → Γ ⊢ τ ⦂ CSort s
                  → Γ ⊢ P ⦂ τ ⇒' ⋆ₑ
                  → Γ ⊢ ε ⦂ τ
                  → Γ ⊢ π ⦂ P · ε
                  → Γ ⊢ [ ε ⦂ τ ∣ π of P ] ⦂ Σ[ τ ] P
Σ-ctor-well-typed {ℓ} {τ} {s} {ε} {Γ} {P} {π} δτ δP δε δπ =
  CT-Abs
    (CT-Abs
      app₂
      (⇒'-well-typed
        (Σ-cont-well-typed δτ δP)
        (CT-Var (Γ⊢⋆⦂□ δτ))
      )
    )
    (Σ-well-typed δτ δP)
  where
  δ↑↑ : Γ ⊢ ε' ⦂ τ'
      → Γ , ⋆ₑ , Σ-cont τ P ⊢ weaken-ε-k 2 ε' ⦂ weaken-ε-k 2 τ'
  δ↑↑ δ = CT-Weaken (CT-Weaken δ (Γ⊢⋆⦂□ δ)) (Σ-cont-well-typed δτ δP)

  app₁ : Γ , ⋆ₑ , Σ-cont τ P ⊢
         CVar zero · weaken-ε-k 2 ε ⦂
         [ zero ↦ weaken-ε-k 2 ε ] (R.act-ε (R.ext suc) (weaken-ε-k 2 P · CVar zero ⇒' CVar (suc zero)))
  app₁ = CT-App (CT-Var (Σ-cont-well-typed δτ δP)) (δ↑↑ δε)

  app₁-lemma : (weaken-ε-k 2 P · weaken-ε-k 2 ε ⇒' CVar (suc zero))
               ≡
               [ zero ↦ weaken-ε-k 2 ε ] (R.act-ε (R.ext suc) (weaken-ε-k 2 P · CVar zero ⇒' CVar (suc zero)))
  app₁-lemma
    rewrite ext-suc-suc-is-suc² (weaken-ε P)
          | replace-weakened-ε-zero (weaken-ε-k 2 ε) (weaken-ε-k 2 P)
          = refl

  app₁' : Γ , ⋆ₑ , Σ-cont τ P ⊢
          CVar zero · weaken-ε-k 2 ε ⦂
          weaken-ε-k 2 P · weaken-ε-k 2 ε ⇒' CVar (suc zero)
  app₁' rewrite app₁-lemma = app₁

  app₂ : Γ , ⋆ₑ , Σ-cont τ P ⊢ CVar zero · weaken-ε-k 2 ε · weaken-ε-k 2 π ⦂ CVar (suc zero)
  app₂ rewrite replace-weakened-ε-zero (weaken-ε-k 2 π) (CVar (suc zero)) = CT-App app₁' (δ↑↑ δπ)

×-well-typed : Γ ⊢ τ₁ ⦂ ⋆ₑ
             → Γ ⊢ τ₂ ⦂ ⋆ₑ
             → Γ ⊢ ⟨ τ₁ × τ₂ ⟩ ⦂ ⋆ₑ
×-well-typed δ₁ δ₂ =
  Σ-well-typed
    δ₁
    (CT-Abs
      (CT-Weaken δ₂ δ₁)
      (CT-Form δ₁ (CT-Weaken (Γ⊢⋆⦂□ δ₁) δ₁))
    )

×-ctor-well-typed : Γ ⊢ τ₁ ⦂ ⋆ₑ
                  → Γ ⊢ τ₂ ⦂ ⋆ₑ
                  → Γ ⊢ ε₁ ⦂ τ₁
                  → Γ ⊢ ε₂ ⦂ τ₂
                  → Γ ⊢ ⟨ ε₁ ⦂ τ₁ × ε₂ ⦂ τ₂ ⟩ ⦂ ⟨ τ₁ × τ₂ ⟩
×-ctor-well-typed {ε₂ = ε₂} δτ₁ δτ₂ δε₁ δε₂ =
  Σ-ctor-well-typed {π = ε₂}
    δτ₁
    (CT-Abs (CT-Weaken δτ₂ δτ₁) (⇒'-well-typed δτ₁ (Γ⊢⋆⦂□ δτ₂)))
    δε₁
    (CT-Conv
      δε₂
      (CT-App
        (CT-Abs
          (CT-Weaken
            δτ₂
            δτ₁
          )
          (CT-Form
            δτ₁
            (CT-Weaken (Γ⊢⋆⦂□ δτ₁) δτ₁)
          )
        )
        δε₁
      )
      (ε-↭β _ _ _)
    )
  where
  ε-↭β : (τ ε ε' : CExpr ℓ)
        → ε ↭β CLam τ (weaken-ε ε) · ε'
  ε-↭β τ ε ε' = subst
                  (_↭β CLam τ (weaken-ε ε) · ε')
                  (replace-weakened-ε-zero ε' ε)
                  (↜-as-↭β CE-AppAbs)

≡̂-well-typed : Γ ⊢ ε₁ ⦂ τ
             → Γ ⊢ ε₂ ⦂ τ
             → Γ ⊢ τ ⦂ ⋆ₑ
             → Γ ⊢ ε₁ ≡̂ ε₂ of τ ⦂ ⋆ₑ
≡̂-well-typed {_} {Γ} {ε₁} {τ} {ε₂} ε₁δ ε₂δ τδ =
  CT-Form
    Γ⊢τ⇒'⋆ₑ
    (×-well-typed ε₁⇒ε₂ ε₂⇒ε₁)
  where
  Γ⊢τ⇒'⋆ₑ : Γ ⊢ τ ⇒' ⋆ₑ ⦂ □ₑ
  Γ⊢τ⇒'⋆ₑ = ⇒'-well-typed τδ (Γ⊢⋆⦂□ τδ)

  ε₁⇒ε₂ : Γ , (τ ⇒' ⋆ₑ) ⊢ (CVar zero · weaken-ε ε₁) ⇒' (CVar zero · weaken-ε ε₂) ⦂ ⋆ₑ
  ε₁⇒ε₂ = ⇒'-well-typed
            (CT-App (CT-Var Γ⊢τ⇒'⋆ₑ) (CT-Weaken ε₁δ Γ⊢τ⇒'⋆ₑ))
            (CT-App (CT-Var Γ⊢τ⇒'⋆ₑ) (CT-Weaken ε₂δ Γ⊢τ⇒'⋆ₑ))

  ε₂⇒ε₁ : Γ , (τ ⇒' ⋆ₑ) ⊢ (CVar zero · weaken-ε ε₂) ⇒' (CVar zero · weaken-ε ε₁) ⦂ ⋆ₑ
  ε₂⇒ε₁ = ⇒'-well-typed
            (CT-App (CT-Var Γ⊢τ⇒'⋆ₑ) (CT-Weaken ε₂δ Γ⊢τ⇒'⋆ₑ))
            (CT-App (CT-Var Γ⊢τ⇒'⋆ₑ) (CT-Weaken ε₁δ Γ⊢τ⇒'⋆ₑ))
