{-# OPTIONS --safe #-}

module Core.Syntax.Derived.Typing where

open import Data.Fin using (zero; suc)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import Core.Syntax
open import Core.Syntax.Derived
open import Core.Syntax.Membership
open import Core.Syntax.Renaming as R
open import Core.Syntax.Renaming.Distributivity as R
open import Core.Syntax.Substitution as S
open import Core.Syntax.Substitution.Stable
open import Core.Derivations
open import Core.Derivations.Lemmas
open import Core.Operational
open import Core.Operational.BetaEquivalence

CT-VarW : Γ ⊢ τ' ⦂ CSort s
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

Σ-cont-well-typed : ∀ {Γ : Ctx ℓ} {P}
                  → Γ ⊢ τ ⦂ CSort s
                  → Γ ⊢ P ⦂ τ ⇒' ⋆ₑ
                  → Γ , ⋆ₑ ⊢ Σ-cont τ P ⦂ ⋆ₑ
Σ-cont-well-typed δτ δP =
  CT-Form
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
  where
  Γ,⋆⊢τ = CT-Weaken δτ (Γ⊢⋆⦂□ δτ)

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
  app₂ = CT-App app₁' (δ↑↑ δπ)

×-cont-well-typed : Γ ⊢ τ₁ ⦂ ⋆ₑ
                  → Γ ⊢ τ₂ ⦂ ⋆ₑ
                  → Γ , ⋆ₑ ⊢ ×-cont τ₁ τ₂ ⦂ ⋆ₑ
×-cont-well-typed δτ₁ δτ₂ =
  ⇒'-well-typed
    (CT-Weaken δτ₁ Γ̂ok)
    (⇒'-well-typed
      (CT-Weaken
        δτ₂
        Γ̂ok
      )
      (CT-Var Γ̂ok)
    )
  where
  Γ̂ok = Γ⊢⋆⦂□ δτ₁

×-well-typed : Γ ⊢ τ₁ ⦂ ⋆ₑ
             → Γ ⊢ τ₂ ⦂ ⋆ₑ
             → Γ ⊢ ⟨ τ₁ × τ₂ ⟩ ⦂ ⋆ₑ
×-well-typed δτ₁ δτ₂ =
  CT-Form
    Γ̂ok
    (CT-Form
      (×-cont-well-typed δτ₁ δτ₂)
      (CT-Weaken
        (CT-Var Γ̂ok)
        (×-cont-well-typed δτ₁ δτ₂)
      )
    )
  where
  Γ̂ok = Γ⊢⋆⦂□ δτ₁

×-ctor-well-typed : Γ ⊢ τ₁ ⦂ ⋆ₑ
                  → Γ ⊢ τ₂ ⦂ ⋆ₑ
                  → Γ ⊢ ε₁ ⦂ τ₁
                  → Γ ⊢ ε₂ ⦂ τ₂
                  → Γ ⊢ ⟨ ε₁ ⦂ τ₁ × ε₂ ⦂ τ₂ ⟩ ⦂ ⟨ τ₁ × τ₂ ⟩
×-ctor-well-typed {_} {Γ} {τ₁} {τ₂} {ε₁} {ε₂} δτ₁ δτ₂ δε₁ δε₂ =
  CT-Abs
    (CT-Abs
      app₂
      (⇒'-well-typed
        (×-cont-well-typed δτ₁ δτ₂)
        (CT-Var (Γ⊢⋆⦂□ δτ₁))
      )
    )
    (×-well-typed δτ₁ δτ₂)
  where
  δ↑↑ : Γ ⊢ ε' ⦂ τ'
      → Γ , ⋆ₑ , ×-cont τ₁ τ₂ ⊢ weaken-ε-k 2 ε' ⦂ weaken-ε-k 2 τ'
  δ↑↑ δ = CT-Weaken (CT-Weaken δ (Γ⊢⋆⦂□ δ)) (×-cont-well-typed δτ₁ δτ₂)

  app₁ : Γ , ⋆ₑ , ×-cont τ₁ τ₂ ⊢
         CVar zero · weaken-ε-k 2 ε₁ ⦂
         [ zero ↦ weaken-ε-k 2 ε₁ ] R.act-ε (R.ext suc) (weaken-ε (weaken-ε τ₂ ⇒' CVar zero))
  app₁ = CT-App (CT-Var (×-cont-well-typed δτ₁ δτ₂)) (δ↑↑ δε₁)

  app₁-lemma : [ zero ↦ weaken-ε-k 2 ε₁ ] R.act-ε (R.ext suc) (weaken-ε (weaken-ε τ₂ ⇒' CVar zero))
               ≡
               (weaken-ε-k 2 τ₂ ⇒' CVar (suc zero))
  app₁-lemma = subst
                (λ τ → [ zero ↦ weaken-ε-k 2 ε₁ ] τ ≡ weaken-ε (weaken-ε τ₂ ⇒' CVar zero))
                (sym (ext-suc-suc-is-suc² (weaken-ε τ₂ ⇒' CVar zero)))
                (replace-weakened-ε-zero (weaken-ε-k 2 ε₁) (weaken-ε (weaken-ε τ₂ ⇒' CVar zero)))

  app₁' : Γ , ⋆ₑ , ×-cont τ₁ τ₂ ⊢
          CVar zero · weaken-ε-k 2 ε₁ ⦂
          weaken-ε-k 2 τ₂ ⇒' CVar (suc zero)
  app₁' = subst (λ τ → Γ , ⋆ₑ , ×-cont τ₁ τ₂ ⊢ CVar zero · weaken-ε-k 2 ε₁ ⦂ τ) app₁-lemma app₁

  app₂ : Γ , ⋆ₑ , ×-cont τ₁ τ₂ ⊢ CVar zero · weaken-ε-k 2 ε₁ · weaken-ε-k 2 ε₂ ⦂ CVar (suc zero)
  app₂ = CT-App app₁' (δ↑↑ δε₂)

{- TODO use these typings when expressing non-dependent pairs as derived forms
   (well, second-order derived forms? :)) of dependent pairs,
   and when normalization is proven.
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
×-ctor-well-typed δτ₁ δτ₂ δε₁ δε₂ =
  Σ-ctor-well-typed
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
      {! !} -- (ε-↭β _ _ _)
    )
  where
  ε-↭β : (τ ε ε' : CExpr ℓ)
        → ε ↭β CLam τ (weaken-ε ε) · ε'
  ε-↭β τ ε ε' = subst
                  (_↭β CLam τ (weaken-ε ε) · ε')
                  (replace-weakened-ε-zero ε' ε)
                  (↜-as-↭β (CE-AppAbs {! !}))
                  -}

≡̂-well-typed : Γ ⊢ ε₁ ⦂ τ
             → Γ ⊢ ε₂ ⦂ τ
             → Γ ⊢ τ ⦂ ⋆ₑ
             → Γ ⊢ ε₁ ≡̂ ε₂ of τ ⦂ ⋆ₑ
≡̂-well-typed {Γ = Γ} {τ = τ} ε₁δ ε₂δ τδ =
  CT-Form
    Γ⊢τ⇒'⋆ₑ
    (×-well-typed ε₁⇒ε₂ ε₂⇒ε₁)
  where
  Γ⊢τ⇒'⋆ₑ : Γ ⊢ τ ⇒' ⋆ₑ ⦂ □ₑ
  Γ⊢τ⇒'⋆ₑ = ⇒'-well-typed τδ (Γ⊢⋆⦂□ τδ)

  0·ε-wf : Γ ⊢ ε ⦂ τ
         → Γ , (τ ⇒' ⋆ₑ) ⊢ CVar zero · weaken-ε ε ⦂ ⋆ₑ
  0·ε-wf εδ = CT-App (CT-Var Γ⊢τ⇒'⋆ₑ) (CT-Weaken εδ Γ⊢τ⇒'⋆ₑ)

  ε₁⇒ε₂ = ⇒'-well-typed (0·ε-wf ε₁δ) (0·ε-wf ε₂δ)
  ε₂⇒ε₁ = ⇒'-well-typed (0·ε-wf ε₂δ) (0·ε-wf ε₁δ)

eq-refl-well-typed : Γ ⊢ τ ⦂ ⋆ₑ
                   → Γ ⊢ ε ⦂ τ
                   → Γ ⊢ eq-refl τ ε ⦂ ε ≡̂ ε of τ
eq-refl-well-typed {Γ = Γ} {τ} {ε} δτ δε =
  CT-Abs
    body-wt
    (CT-Form
      ⇒'-wf
      type-wf
    )
  where
  id-fun = CLam (CVar zero · weaken-ε ε) (CVar zero)
  id-fun-type = CVar zero · weaken-ε ε ⇒' CVar zero · weaken-ε ε

  ⇒'-wf = ⇒'-well-typed δτ (Γ⊢⋆⦂□ δτ)
  0·ε-wf = CT-App
            (CT-Var ⇒'-wf)
            (CT-Weaken δε ⇒'-wf)
  id-fun-type-wf = ⇒'-well-typed 0·ε-wf 0·ε-wf
  id-fun-wf = CT-Abs (CT-Var 0·ε-wf) id-fun-type-wf

  type-wf : Γ , (τ ⇒' ⋆ₑ) ⊢ ⟨ id-fun-type × id-fun-type ⟩ ⦂ ⋆ₑ
  type-wf = ×-well-typed id-fun-type-wf id-fun-type-wf

  body-wt : Γ , (τ ⇒' ⋆ₑ) ⊢
            ⟨ id-fun ⦂ id-fun-type × id-fun ⦂ id-fun-type ⟩ ⦂
            ⟨ id-fun-type × id-fun-type ⟩
  body-wt = ×-ctor-well-typed id-fun-type-wf id-fun-type-wf id-fun-wf id-fun-wf
