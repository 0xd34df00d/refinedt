module Surface.Theorems.Thinning where

open import Data.Vec.Relation.Unary.All renaming (map to All-map)

open import Surface.Syntax
open import Surface.Derivations
open import Sublist

twfThinning : Γ ⊂ Γ' → Γ' ok → (Γ ⊢' τ)    → (Γ' ⊢' τ)
tThinning   : Γ ⊂ Γ' → Γ' ok → (Γ ⊢ ε ⦂ τ) → (Γ' ⊢ ε ⦂ τ)

twfThinning ⊂-prf Γ'ok (TWF-TrueRef _) = TWF-TrueRef Γ'ok
twfThinning ⊂-prf Γ'ok (TWF-Base ε₁δ ε₂δ) = let expCtxOk = TCTX-Bind Γ'ok (TWF-TrueRef Γ'ok)
                                             in TWF-Base (tThinning (PrependBoth ⊂-prf) expCtxOk ε₁δ) (tThinning (PrependBoth ⊂-prf) expCtxOk ε₂δ)
twfThinning ⊂-prf Γ'ok (TWF-Conj ρ₁ ρ₂) = TWF-Conj (twfThinning ⊂-prf Γ'ok ρ₁) (twfThinning ⊂-prf Γ'ok ρ₂)
twfThinning ⊂-prf Γ'ok (TWF-Arr argδ resδ) = TWF-Arr
                                                (twfThinning ⊂-prf Γ'ok argδ)
                                                (twfThinning (PrependBoth ⊂-prf) (TCTX-Bind Γ'ok (twfThinning ⊂-prf Γ'ok argδ)) resδ)
twfThinning ⊂-prf Γ'ok (TWF-ADT consδs) = TWF-ADT (All-map (twfThinning ⊂-prf Γ'ok) consδs)

tThinning ⊂-prf Γ'ok x = {! x !}
