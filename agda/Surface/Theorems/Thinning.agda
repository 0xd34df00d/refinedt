module Surface.Theorems.Thinning where

open import Data.Vec.Relation.Unary.All renaming (map to All-map)

open import Surface.Syntax
open import Surface.Derivations
open import Sublist

twf-thinning : Γ ⊂ Γ' → Γ' ok → (Γ ⊢' τ)    → (Γ' ⊢' τ)
t-thinning   : Γ ⊂ Γ' → Γ' ok → (Γ ⊢ ε ⦂ τ) → (Γ' ⊢ ε ⦂ τ)

twf-thinning ⊂-prf Γ'ok (TWF-TrueRef _) = TWF-TrueRef Γ'ok
twf-thinning ⊂-prf Γ'ok (TWF-Base ε₁δ ε₂δ) = let expCtxOk = TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)
                                              in TWF-Base (t-thinning (PrependBoth ⊂-prf) expCtxOk ε₁δ) (t-thinning (PrependBoth ⊂-prf) expCtxOk ε₂δ)
twf-thinning ⊂-prf Γ'ok (TWF-Conj ρ₁ ρ₂) = TWF-Conj (twf-thinning ⊂-prf Γ'ok ρ₁) (twf-thinning ⊂-prf Γ'ok ρ₂)
twf-thinning ⊂-prf Γ'ok (TWF-Arr argδ resδ) = TWF-Arr
                                                (twf-thinning ⊂-prf Γ'ok argδ)
                                                (twf-thinning (PrependBoth ⊂-prf) (TCTX-Bind Γ'ok (twf-thinning ⊂-prf Γ'ok argδ)) resδ)
twf-thinning {Γ} {Γ'} ⊂-prf Γ'ok (TWF-ADT consδs)= TWF-ADT (map-cons consδs)
  where
    map-cons : {cons : ADTCons n} → All (Γ ⊢'_) cons → All (Γ' ⊢'_) cons
    map-cons [] = []
    map-cons (px ∷ pxs) = twf-thinning ⊂-prf Γ'ok px ∷ map-cons pxs

tThinning ⊂-prf Γ'ok x = {! x !}
