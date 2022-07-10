{-# OPTIONS --safe #-}

module Common.WF where

open import Data.Fin using (zero; suc; #_; Fin)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Vec
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

infixr 20 _⊕_
_⊕_ : ℕ → ℕ → ℕ
_⊕_ = _⊔_

₁≤₂ : ∀ m n → m ≤ m ⊕ n
₁≤₂ = m≤m⊔n

₂≤₂ : ∀ m n → n ≤ m ⊕ n
₂≤₂ = m≤n⊔m

₁≤₃ : ∀ m n k → m ≤ m ⊕ n ⊕ k
₁≤₃ m n k = ₁≤₂ _ _

₂≤₃ : ∀ m n k → n ≤ m ⊕ n ⊕ k
₂≤₃ m n k = ≤-trans (₁≤₂ n k) (₂≤₂ m (n ⊔ k))

₃≤₃ : ∀ m n k → k ≤ m ⊕ n ⊕ k
₃≤₃ m n k = ≤-trans (₂≤₂ n k) (₂≤₂ m (n ⊔ k))

₁≤₄ : ∀ n₁ n₂ n₃ n₄ → n₁ ≤ n₁ ⊕ n₂ ⊕ n₃ ⊕ n₄
₁≤₄ n₁ n₂ n₃ n₄ = ₁≤₂ _ _

₂≤₄ : ∀ n₁ n₂ n₃ n₄ → n₂ ≤ n₁ ⊕ n₂ ⊕ n₃ ⊕ n₄
₂≤₄ n₁ n₂ n₃ n₄ = ₂≤₃ n₁ n₂ (n₃ ⊔ n₄)

₃≤₄ : ∀ n₁ n₂ n₃ n₄ → n₃ ≤ n₁ ⊕ n₂ ⊕ n₃ ⊕ n₄
₃≤₄ n₁ n₂ n₃ n₄ = ≤-trans (₁≤₂ n₃ n₄) (₃≤₃ n₁ n₂ (n₃ ⊔ n₄))

₄≤₄ : ∀ n₁ n₂ n₃ n₄ → n₄ ≤ n₁ ⊕ n₂ ⊕ n₃ ⊕ n₄
₄≤₄ n₁ n₂ n₃ n₄ = ≤-trans (₂≤₂ n₃ n₄) (₃≤₃ n₁ n₂ (n₃ ⊔ n₄))

≤₄ : ∀ {n₁ n₂ n₃ n₄}
   → (v : Vec ℕ 4)
   → ⦃ v ≡ n₁ ∷ n₂ ∷ n₃ ∷ n₄ ∷ [] ⦄
   → (ι : Fin 4)
   → lookup v ι ≤ n₁ ⊕ n₂ ⊕ n₃ ⊕ n₄
≤₄ {n₁} {n₂} {n₃} {n₄} _ ⦃ refl ⦄ = λ where zero                   → ₁≤₄ n₁ n₂ n₃ n₄
                                            (suc zero)             → ₂≤₄ n₁ n₂ n₃ n₄
                                            (suc (suc zero))       → ₃≤₄ n₁ n₂ n₃ n₄
                                            (suc (suc (suc zero))) → ₄≤₄ n₁ n₂ n₃ n₄

<₄ : ∀ {n₁ n₂ n₃ n₄}
   → (v : Vec ℕ 4)
   → ⦃ v ≡ n₁ ∷ n₂ ∷ n₃ ∷ n₄ ∷ [] ⦄
   → (ι : Fin 4)
   → lookup v ι < suc (n₁ ⊕ n₂ ⊕ n₃ ⊕ n₄)
<₄ v ι = s≤s (≤₄ v ι)
