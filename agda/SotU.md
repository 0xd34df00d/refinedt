Misc notes about the obstacles with the current (or important past) implementation,
and the rationales for various design decisions.

## Translation

A proper notion of translation proves to be surprisingly hard.
The root cause seems to be that our Surface language has subtyping, while our Core doesn't.

### Surface

What implications does subtyping have?
Subtyping breaks either uniqueness of typing (further named UoT) or type preservation (or both).

UoT breaks since one can stick `T-Sub` rules arbitrarily over the root of the (minimal) derivation tree.

Type preservation breaks since if we have
```idris
f : {ν : Int | ν > 0} → {ν : Int | ν > 0}
f x = x
```
(the identity function restricted to positive integers), the type of `f 5` is `{ν : Int | ν > 0}`,
while `f 5` evaulates to `5`, whose type is more precise: `{ν : Int | ν = 5}`.

This can be remedied somewhat by indexing the (term) typing derivations by whether they end with a `T-Sub` rule.
That is, a relation `Γ ⊢ ε ⦂ τ` becomes `Γ ⊢[ κ ] ε ⦂ τ` where κ ∊ { `t-sub`, `not-t-sub` }.
That is, for `Γ ⊢[ not-t-sub ] ε ⦂ τ` we know that it doesn't end with a `T-Sub` rule,
and for `Γ ⊢[ t-sub ] ε ⦂ τ` we do know that it ends with a `T-Sub`.

If we're careful to craft our derivations (namely, by requiring `not-t-sub` in all inductive usages of the relation
_except_ the function application, where the RHS _must be_ `t-sub`), we can prove three metatheorems:

1. UoT for `not-t-sub`:
   given `Γ ⊢[ not-t-sub ] ε ⦂ τ₁` and `Γ ⊢[ not-t-sub ] ε ⦂ τ₂`, we know `τ₁ ≡ τ₂`.
2. UoT-δ for `t-sub` (where UoT-δ stands for "uniqueness of typing _derivations_"):
   given `εδ₁ : Γ ⊢[ t-sub ] ε ⦂ τ` and `εδ₂ : Γ ⊢[ t-sub ] ε ⦂ τ`, we know that `εδ₁ ≡ εδ₂`.
   This is a very useful metatheoretical property when formalizing the translation in Agda.
3. Full typing preservation: if `Γ ⊢[ t-sub ] ε ⦂ τ` and `ε ↝ ε'`, then `Γ ⊢[ t-sub ] ε' ⦂ τ`.

Note that (3) doesn't hold for `not-t-sub`: evaluation there produces a _subtype_ of the original type.

Also, (1) and (2) also extend to the type well-formedness (`Γ ⊢ τ`) and context well-formedness (`Γ ok`) judgements.
