module Surface.Derivations.Algorithmic.ToIntermediate.Translation where

open import Data.Fin using (suc; zero)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)

open import Surface.Syntax as S
import Surface.Syntax.Membership as S
import Surface.Syntax.Renaming as SR
import Surface.Syntax.Substitution as S
open import Surface.Derivations.Algorithmic as S
open import Surface.Derivations.Algorithmic.Theorems.Agreement
open import Surface.Derivations.Algorithmic.Theorems.Thinning
open import Surface.Derivations.Algorithmic.Theorems.Uniqueness

open import Intermediate.Syntax as I
open import Intermediate.Syntax.Short
open import Intermediate.Syntax.Renaming as IR
open import Intermediate.Syntax.Substitution as IS
import Intermediate.Syntax.Membership as I
import Intermediate.Derivations.Algorithmic as I

open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Aliases
open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Subst
open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.Typed
open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.μ-weakening
open import Surface.Derivations.Algorithmic.ToIntermediate.Translation.μ-subst

μ-τ-computed : {τˢ : SType ℓ}
             → (εδ : Γˢ ⊢[ θˢ , E of κ ] εˢ ⦂ τˢ)
             → IType ℓ
μ-τ-computed (T-App ε₁δ (T-Sub ε₂δ _ <:δ) _ _)
  with TWF-Arr _ τ₂δ ← Γ⊢ε⦂τ-⇒-Γ⊢τ ε₁δ
     = [ zero ↦τⁱ μ-<: <:δ ∙ μ-ε ε₂δ ] μ-τ τ₂δ
μ-τ-computed (T-Abs (TWF-Arr τ₁δ _) εδ) = μ-τ τ₁δ ⇒ μ-τ-computed εδ
μ-τ-computed εδ = μ-τ (Γ⊢ε⦂τ-⇒-Γ⊢τ εδ)

μ-τ-same : (τ₁δ τ₂δ : Γˢ ⊢[ θˢ , E ] τˢ)
         → μ-τ τ₁δ ≡ μ-τ τ₂δ
μ-τ-same τ₁δ τ₂δ = cong μ-τ (unique-Γ⊢τ τ₁δ τ₂δ)

μ-τ-computed-compat : {τ₁ˢ : SType ℓ}
                    → (ε₂δ : Γˢ ⊢[ θˢ , E of t-sub ] ε₂ˢ ⦂ τ₁ˢ)
                    → (ε₁δ : Γˢ ⊢[ θˢ , E of not-t-sub ] ε₁ˢ ⦂ τ₁ˢ ⇒ τ₂ˢ)
                    → (τ₁ⁱ ⇒ τ₂ⁱ ≡ μ-τ-computed ε₁δ)
                    → τ₁ⁱ ≡ μ-τ-computed ε₂δ
μ-τ-computed-compat (T-Sub _ τ₁δ _) (T-Var Γok ∈) eq
  with TWF-Arr τ₁δ' _ ← τ∈Γ-⇒-Γ⊢τ Γok ∈
     | refl ← eq
     = μ-τ-same τ₁δ' τ₁δ
μ-τ-computed-compat (T-Sub _ τ₁δ _) (T-Abs (TWF-Arr τ₁δ' _) ε₁δ) refl = μ-τ-same τ₁δ' τ₁δ
μ-τ-computed-compat (T-Sub _ τ₁δ _) (T-App ε₁δ (T-Sub ε₂δ x <:δ) resτ-≡ resτδ) eq
  with TWF-Arr _ τ₂δ ← Γ⊢ε⦂τ-⇒-Γ⊢τ ε₁δ
     = {! !}
μ-τ-computed-compat (T-Sub _ τ₁δ _) (T-Case resδ ε₁δ branches-well-typed) eq = {! !}

private
  μ-τ-lemma₁ : (τδ : Γˢ ,ˢ τ'ˢ ⊢[ θˢ , E ] SR.weaken-τ τˢ)
             → (τδ' : Γˢ ⊢[ θˢ , E ] τˢ)
             → (τ'δ : Γˢ ⊢[ θˢ , E ] τ'ˢ)
             → μ-τ τδ ≡ IR.weaken-τ (μ-τ τδ')
  μ-τ-lemma₁ τδ τδ' τ'δ = let Γok = Γ⊢τ-⇒-Γok τδ'
                           in trans
                                (cong μ-τ (unique-Γ⊢τ τδ (Γ⊢τ-weakening Γok τ'δ τδ')))
                                (μ-τ-weakening-commutes Γok τ'δ τδ')

  μ-∈ : (Γok : Γˢ ok[ θˢ , E ])
      → (τδ : Γˢ ⊢[ θˢ , E ] τˢ)
      → (τˢ S.∈ Γˢ at ι)
      → (μ-τ τδ I.∈ μ-Γ Γok at ι)
  μ-∈ (TCTX-Bind _ τδ') τδ (S.∈-zero refl) = I.∈-zero (μ-τ-lemma₁ τδ τδ' τδ')
  μ-∈ (TCTX-Bind Γok _) τδ (S.∈-suc refl ∈)
    = let τδ' = τ∈Γ-⇒-Γ⊢τ Γok ∈
          Γ,τ-ok = Γ⊢τ-⇒-Γok τδ
          τ'δ = case Γ,τ-ok of λ where (TCTX-Bind _ τ'δ) → τ'δ
       in I.∈-suc (μ-τ-lemma₁ τδ τδ' τ'δ) (μ-∈ Γok τδ' ∈)

mutual
  μ-ε-δ : {τˢ : SType ℓ}
        → (εδ : Γˢ ⊢[ θˢ , E of κ ] εˢ ⦂ τˢ)
        → [ θⁱ ] μ-Γ (Γ⊢ε⦂τ-⇒-Γok εδ) ⊢ μ-ε εδ ⦂ μ-τ-computed εδ
  μ-ε-δ (T-Unit Γok) = T-Unit (μ-Γ-δ Γok)
  μ-ε-δ (T-Var Γok ∈) = T-Var (μ-Γ-δ Γok) (μ-∈ Γok (τ∈Γ-⇒-Γ⊢τ Γok ∈) ∈)
  μ-ε-δ (T-Abs τ₁⇒τ₂δ@(TWF-Arr τ₁δ τ₂δ) εδ)
    = let εδⁱ = μ-ε-δ εδ
          εδⁱ = subst-[Γ]⊢ε⦂τ _ _   εδⁱ
       in T-Abs {! !} εδⁱ
  μ-ε-δ {θⁱ = θⁱ} (T-App ε₁δ (T-Sub ε₂δ _ <:δ) refl resτδ)
    with τ₁⇒τ₂δ@(TWF-Arr τ₁δ τ₂δ) ← Γ⊢ε⦂τ-⇒-Γ⊢τ ε₁δ
    = let ε₁δⁱ = μ-ε-δ {θⁱ = θⁱ} ε₁δ
          ε₂δⁱ = μ-ε-δ {θⁱ = θⁱ} ε₂δ
       in T-App {! !} {! !} {! !} {! !}

{-
  μ-ε-δ : {τˢ : SType ℓ}
        → (εδ : Γˢ ⊢[ θˢ , E of κ ] εˢ ⦂ τˢ)
        → [ θⁱ ] μ-Γ (Γ⊢ε⦂τ-⇒-Γok εδ) ⊢ μ-ε εδ ⦂ μ-τ (Γ⊢ε⦂τ-⇒-Γ⊢τ εδ)
  μ-ε-δ (T-Unit Γok) = T-Unit (μ-Γ-δ Γok)
  μ-ε-δ (T-Var Γok ∈) = T-Var (μ-Γ-δ Γok) (μ-∈ Γok (τ∈Γ-⇒-Γ⊢τ Γok ∈) ∈)
  μ-ε-δ (T-Abs τ₁⇒τ₂δ@(TWF-Arr τ₁δ τ₂δ) εδ)
    = let εδⁱ = μ-ε-δ εδ
          εδⁱ = subst-Γ⊢ε⦂[τ] _ τ₂δ εδⁱ
          εδⁱ = subst-[Γ]⊢ε⦂τ _ _   εδⁱ
       in T-Abs (μ-τ-δ τ₁⇒τ₂δ) εδⁱ
  μ-ε-δ (T-App ε₁δ ε₂δ refl resτδ)
    with τ₁⇒τ₂δ@(TWF-Arr τ₁δ τ₂δ) ← Γ⊢ε⦂τ-⇒-Γ⊢τ ε₁δ
    = let ε₁δⁱ = μ-ε-δ ε₁δ
          ε₁δⁱ = subst-Γ⊢ε⦂[τ] (Γ⊢ε⦂τ-⇒-Γ⊢τ ε₁δ) τ₁⇒τ₂δ ε₁δⁱ
          ε₂δⁱ = μ-ε-δ ε₂δ
          ε₂δⁱ = subst-Γ⊢ε⦂[τ] _ τ₁δ ε₂δⁱ
          ε₂δⁱ = subst-[Γ]⊢ε⦂τ _ _   ε₂δⁱ
          resτδⁱ = subst-[Γ]⊢τ _ _ (μ-τ-δ resτδ)
       in T-App ε₁δⁱ ε₂δⁱ (μ-τ-sub-front-distr {! ε₂δ !} τ₂δ resτδ) resτδⁱ
  μ-ε-δ (T-Case resδ εδ branches-well-typed) = {! !}
  μ-ε-δ (T-Con ≡-prf εδ adtτ) = {! !}
  μ-ε-δ (T-Sub εδ τ'δ <:δ)
    = let εδⁱ = μ-ε-δ εδ
          <:δⁱ = μ-<:-δ (Γ⊢ε⦂τ-⇒-Γok εδ) <:δ
          <:δⁱ = subst-Γ⊢ε⦂[τ₁]⇒[τ₂] (Γ⊢τ'<:τ-⇒-Γ⊢τ' <:δ) (Γ⊢ε⦂τ-⇒-Γ⊢τ εδ) (Γ⊢τ'<:τ-⇒-Γ⊢τ <:δ) τ'δ <:δⁱ
          τ'δⁱ = subst-[Γ]⊢τ _ _ (μ-τ-δ τ'δ)
       in T-App <:δⁱ εδⁱ {! !} τ'δⁱ
       -}

  μ-τ-δ : {τˢ : SType ℓ}
        → (τδ : Γˢ ⊢[ θˢ , E ] τˢ)
        → [ θⁱ ] μ-Γ (Γ⊢τ-⇒-Γok τδ) ⊢ μ-τ τδ
        {-
  μ-τ-δ (TWF-TrueRef Γok) = TWF-TrueRef (μ-Γ-δ Γok)
  μ-τ-δ (TWF-Base ε₁δ ε₂δ)
    with Γ,τ-ok@(TCTX-Bind Γok (TWF-TrueRef _)) ← Γ⊢ε⦂τ-⇒-Γok ε₁δ
    = let ε₁δⁱ = μ-ε-δ ε₁δ
          ε₁δⁱ = subst-[Γ]⊢ε⦂τ _ Γ,τ-ok ε₁δⁱ
          ε₁δⁱ = subst-Γ⊢ε⦂[τ] _ (TWF-TrueRef Γ,τ-ok) ε₁δⁱ
          --
          ε₂δⁱ = μ-ε-δ ε₂δ
          ε₂δⁱ = subst-[Γ]⊢ε⦂τ _ Γ,τ-ok ε₂δⁱ
          ε₂δⁱ = subst-Γ⊢ε⦂[τ] _ (TWF-TrueRef Γ,τ-ok) ε₂δⁱ
       in TWF-Base ε₁δⁱ ε₂δⁱ
  μ-τ-δ (TWF-Conj τ₁δ τ₂δ) = TWF-Conj (μ-τ-δ τ₁δ) (subst-[Γ]⊢τ _ _ (μ-τ-δ τ₂δ))
  μ-τ-δ (TWF-Arr τ₁δ τ₂δ) = TWF-Arr (μ-τ-δ τ₁δ) (subst-[Γ]⊢τ _ _ (μ-τ-δ τ₂δ))
  μ-τ-δ (TWF-ADT consδs) = {! !}
  -}

  μ-<:-δ : {τ'ˢ τˢ : SType ℓ}
         → (Γok : Γˢ ok[ θˢ , E ])
         → (<:δ : Γˢ ⊢[ θˢ , E ] τ'ˢ <: τˢ)
         → (let τ'δ = Γ⊢τ'<:τ-⇒-Γ⊢τ' <:δ)
         → (let τδ  = Γ⊢τ'<:τ-⇒-Γ⊢τ  <:δ)
         → [ θⁱ ] μ-Γ Γok ⊢ μ-<: <:δ ⦂ μ-τ τ'δ ⇒ IR.weaken-τ (μ-τ τδ)
  μ-<:-δ Γok (ST-Base is-just ρ₁δ ρ₂δ) = {! !}
  μ-<:-δ Γok (ST-Arr <:δ <:δ₁ (enriched τ₁⇒τ₂'δ) (enriched τ₁'⇒τ₂δ@(TWF-Arr _ _))) = {! !}

  μ-Γ-δ : (Γok : Γˢ ok[ θˢ , E ])
        → [ θⁱ ] μ-Γ Γok ok
  μ-Γ-δ TCTX-Empty = TCTX-Empty
  μ-Γ-δ (TCTX-Bind Γok τδ) = TCTX-Bind (μ-Γ-δ Γok) (subst-[Γ]⊢τ _ _ (μ-τ-δ τδ))


{-
-- A value of type μ-WellTyped εδˢ τⁱ is a witness that μ-ε εδˢ has type τⁱ.
data μ-WellTyped {ℓ} {θˢ}
                 : {τˢ : SType ℓ}
                 → (εδ : Γˢ ⊢[ θˢ , E of κ ] εˢ ⦂ τˢ)
                 → (τⁱ : IType ℓ)
                 → Set where
  μ-T-Unit : (Γok : Γˢ ok[ θˢ , E ])
           → μ-WellTyped (T-Unit Γok) ⟨ BUnit ∣ Τ ⟩
  μ-T-Var  : (Γok : Γˢ ok[ θˢ , E ])
           → (∈ : τˢ S.∈ Γˢ at ι)
           → (τⁱ-≡ : τⁱ ≡ μ-τ (τ∈Γ-⇒-Γ⊢τ Γok ∈))
           → μ-WellTyped (T-Var Γok ∈) τⁱ
  μ-Τ-Abs  : (arrδ : Γˢ ⊢[ θˢ , E ] τ₁ˢ ⇒ τ₂ˢ)
           → (bodyδ : Γˢ , τ₁ˢ ⊢[ θˢ , E of not-t-sub ] εˢ ⦂ τ₂ˢ)
           → (τⁱ-≡ : τⁱ ≡ μ-τ arrδ)
           → μ-WellTyped (T-Abs arrδ bodyδ) τⁱ
  μ-T-App  : (ε₁δ : Γˢ ⊢[ θˢ , E of not-t-sub ] ε₁ˢ ⦂ τ₁ˢ ⇒ τ₂ˢ)
           → (ε₂δ : Γˢ ⊢[ θˢ , E of t-sub ] ε₂ˢ ⦂ τ₁ˢ)
           → (resτˢ-≡ : τˢ ≡ [ zero ↦τˢ ε₂ˢ ] τ₂ˢ)
           → (τδ : Γˢ ⊢[ θˢ , E ] τˢ)
           → (τⁱ-≡ : τⁱ ≡ [ zero ↦τⁱ μ-ε ε₂δ ] τ₂ⁱ)
           → μ-WellTyped ε₁δ (τ₁ⁱ ⇒ τ₂ⁱ)
           → μ-WellTyped ε₂δ τ₁ⁱ
           → μ-WellTyped (T-App ε₁δ ε₂δ resτˢ-≡ τδ) τⁱ
  μ-T-Sub  : (εδ  : Γˢ ⊢[ θˢ , E of not-t-sub ] εˢ ⦂ τ'ˢ)
           → (τδ : Γˢ ⊢[ θˢ , E ] τˢ)
           → (<:δ : Γˢ ⊢[ θˢ , E ] τ'ˢ <: τˢ)
           → (τⁱ-≡ : τⁱ ≡ μ-τ τδ)
           → μ-WellTyped (T-Sub εδ τδ <:δ) τⁱ

μ-τ-same : (τ₁δ τ₂δ : Γˢ ⊢[ θˢ , E ] τˢ)
         → μ-τ τ₁δ ≡ μ-τ τ₂δ
μ-τ-same τ₁δ τ₂δ = cong μ-τ (unique-Γ⊢τ τ₁δ τ₂δ)

μ-WellTyped-lemma₁ : {ε₁δ : Γˢ ⊢[ θˢ , E of not-t-sub ] ε₁ˢ ⦂ τ₁ˢ ⇒ τ₂ˢ}
                   → {ε₂δ : Γˢ ⊢[ θˢ , E of t-sub ] ε₂ˢ ⦂ τ₁ˢ}
                   → μ-WellTyped ε₂δ τ₁'ⁱ
                   → μ-WellTyped ε₁δ (τ₁ⁱ ⇒ τ₂ⁱ)
                   → τ₁ⁱ ≡ τ₁'ⁱ
μ-WellTyped-lemma₁ (μ-T-Sub _ τ₁δ _ refl) (μ-T-Var Γok ∈ τⁱ-≡)
  with TWF-Arr τ₁δ' _ ← τ∈Γ-⇒-Γ⊢τ Γok ∈
     | refl ← τⁱ-≡
     = μ-τ-same τ₁δ' τ₁δ
μ-WellTyped-lemma₁ (μ-T-Sub _ τ₁δ _ refl) (μ-Τ-Abs (TWF-Arr τ₁δ' _) _ refl) = μ-τ-same τ₁δ' τ₁δ
μ-WellTyped-lemma₁ (μ-T-Sub _ τ₁δ _ refl) (μ-T-App {ε₂ˢ = ε₂ˢ} _ ε₂δ resτˢ-≡ τ₁δ' x _ _) = {! !}

μ-ε-δ : {τˢ : SType ℓ}
      → (εδ : Γˢ ⊢[ θˢ , E of κ ] εˢ ⦂ τˢ)
      → ∃[ τⁱ ] (μ-WellTyped εδ τⁱ)
μ-ε-δ (T-Unit Γok) = ⟨ _ , μ-T-Unit Γok ⟩
μ-ε-δ (T-Var Γok ∈) = ⟨ _ , μ-T-Var Γok ∈ refl ⟩
μ-ε-δ (T-Abs arrδ εδ) = {! !}
μ-ε-δ (T-App ε₁δ ε₂δ refl _)
  with μ-ε-δ ε₁δ
     | μ-ε-δ ε₂δ
... | ⟨ τ₁ⁱ ⇒ τ₂ⁱ , ε₁δ-δ ⟩
    | ⟨ τ₁'ⁱ , ε₂δ-δ ⟩
    = ⟨ _ , μ-T-App ε₁δ ε₂δ refl _ refl ε₁δ-δ {! !} ⟩
... | ⟨ ⟨ b ∣ ρ ⟩ , ε₁δ-δ ⟩ | _ = {! !} -- provably absurd
... | ⟨ ⊍ cons , ε₁δ-δ ⟩ | _ = {! !} -- ditto
μ-ε-δ (T-Case resδ εδ branches-well-typed) = {! !}
μ-ε-δ (T-Con ≡-prf εδ adtτ) = {! !}
μ-ε-δ (T-Sub εδ τ'δ <:δ) = {! !}
-}

