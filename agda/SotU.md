Misc notes about the obstacles with the current (or important past) implementation,
and the rationales for various design decisions.

## Translation

A proper notion of translation (where translation commutes with evaluation) proves to be surprisingly hard.
The root cause seems to be that our Surface language has subtyping, while our Core doesn't.

### Surface

#### High-level meta-properties

What implications does subtyping have?
Subtyping breaks either uniqueness of typing (further named UoT) or type preservation (or both).

##### Why is it important?

Clearly, translating any type system without type preservation to λC is doomed to fail,
since evaluation in λC preserves typing (modulo β-equivalence, which is, unlike subtyping, a symmetric relation).
Thus, translation/evaluation commutativity just won't hold.

Translating a type system without the former is not provably impossible,
but it's non-trivial to formalize, and that's something I failed to do.
The problem is that the translation looks not just at the terms, but at term typing derivations,
and, in short, when proving the translation `μ-ε` makes sense,
we need to prove that `εδ₁ : Γ ⊢ ε ⦂ τ` and `εδ₂ : Γ ⊢ ε ⦂ τ` implies `μ-ε εδ₁ ≡ μ-ε εδ₂`.
Without uniqueness of typing this clearly doesn't hold.

In fact, an even weaker property is required here:
uniqueness of typing _derivations_ (further named UoT-δ) is sufficient.
That is, it's sufficient to have `εδ₁ ≡ εδ₂` given `εδ₁ : Γ ⊢ ε ⦂ τ` and `εδ₂ : Γ ⊢ ε ⦂ τ`.

##### Why does it break?

UoT breaks since one can stick `T-Sub` rules arbitrarily over the root of the (minimal) derivation tree.

Type preservation breaks since if we have
```idris
f : {ν : Int | ν > 0} → {ν : Int | ν > 0}
f x = x
```
(the identity function restricted to positive integers), the type of `f 5` is `{ν : Int | ν > 0}`,
while `f 5` evaluates to `5`, whose type is more precise: `{ν : Int | ν = 5}`.

##### Can we regain these properties in the Surface language?

This can be remedied somewhat by indexing the (term) typing derivations by whether they end with a `T-Sub` rule.
That is, a relation `Γ ⊢ ε ⦂ τ` becomes `Γ ⊢[ κ ] ε ⦂ τ` where κ ∊ { `t-sub`, `not-t-sub` }.
That is, for `Γ ⊢[ not-t-sub ] ε ⦂ τ` we know that it doesn't end with a `T-Sub` rule,
and for `Γ ⊢[ t-sub ] ε ⦂ τ` we do know that it ends with a `T-Sub`.

If we're careful to craft our derivations (namely, by requiring `not-t-sub` in all inductive usages of the relation
_except_ the function application, where the RHS _must be_ `t-sub`), we can prove three metatheorems:

1. UoT for `not-t-sub`:
   given `Γ ⊢[ not-t-sub ] ε ⦂ τ₁` and `Γ ⊢[ not-t-sub ] ε ⦂ τ₂`, we know `τ₁ ≡ τ₂`.
2. UoT-δ for `t-sub`:
   given `εδ₁ : Γ ⊢[ t-sub ] ε ⦂ τ` and `εδ₂ : Γ ⊢[ t-sub ] ε ⦂ τ`, we know that `εδ₁ ≡ εδ₂`.
   This obviously holds for `not-t-sub` as well, so it could be generalized to arbitrary `κ`.
3. Full typing preservation: if `Γ ⊢[ t-sub ] ε ⦂ τ` and `ε ↝ ε'`, then `Γ ⊢[ t-sub ] ε' ⦂ τ`.

Note that (3) doesn't hold for `not-t-sub`: evaluation there produces a _subtype_ of the original type.

Also, (1) and (2) also extend to the type well-formedness (`Γ ⊢ τ`) and context well-formedness (`Γ ok`) judgements.

This is almost like algorithmic typing for a type system with subtyping (as described in TAPL, for instance),
but it allows for some freedom at the root of the tree if `κ ~ t-sub`, which enables type preservation to hold.

Also, note that the type system indexed by this `κ` thing is a (strict) subset of a usual declarative typing system,
and it's sufficiently close to be a proper algorithmic type system (especially when one considers `κ ~ not-t-sub`).
In a sense, we haven't made our lifes harder:
all the problems we might have with this formalization would have arisen with some usual unindexed one,
since they would be just a special case of the usual one.

Anyway, all this almost does the trick. _Almost_.

#### What translation properties do we need?

One useful property is that if we have `εδ : Γ ⊢ ε ⦂ τ`
(and, consequently, `Γok : Γ ok` and `τδ : Γ ⊢ τ` due to the agreement lemmas),
then the translated term in the translated context has translated type.
Or, in funny symbols, `μ-Γ Γok ⊢ᶜ μ-ε εδ ⦂ μ-τ τδ`
(where `_⊢ᶜ_⦂_` is the Core derivation relation).

In fact, I see this as the only reasonable way to express "a translation of a well-typed surface term is well-typed".

#### Translating the subtyping witness

Now, how does the translation of the `T-App` Surface typing rule work out?
The rule itself states, modulo technicalities,
```agda
  T-App : (ε₁δ : Γ ⊢[ not-t-sub ] ε₁ ⦂ τ₁ ⇒ τ₂)
        → (ε₂δ : Γ ⊢[ t-sub ] ε₂ ⦂ τ₁)
        → Γ ⊢[ not-t-sub ] SApp ε₁ ε₂ ⦂ [ zero ↦τ ε₂ ] τ₂
```
Due to the `κ` indices we know that `ε₂δ` ends with a `T-Sub`, where `T-Sub` is roughly
```agda
  T-Sub : (εδ : Γ ⊢[ not-t-sub ] ε ⦂ τ')
        → (<:δ : Γ ⊢ τ' <: τ)
        → Γ ⊢[ t-sub ] ε ⦂ τ
```
The subtyping relation `<:δ : Γ ⊢ τ' <: τ` gets translated to a (Core) function `μ-<: <:δ` of the type `Π τ'ᶜ. τᶜ`,
where `τᶜ` is the translation of the witness of (surface) type `τ` being well-formed.

Overall, `ε₂δ` gets translated to `μ-<: <:δ · μ-ε εδ`
(I'm using `·` for Core application `CApp` because there will be more of them).

On the other hand, how do we translate `SApp ε₁ ε₂`?
I see no other way except `μ-ε ε₁δ · μ-ε ε₂δ`.
Expanding the translation for `μ-ε ε₂δ` we get `μ-ε ε₁δ · (μ-<: <:δ · μ-ε εδ)`.

What's the type of `μ-ε ε₁δ`?
Of course, it's `μ-τ τ₁⇒τ₂δ`, where `τ₁⇒τ₂δ` is the derivation of `τ₁ ⇒ τ₂` being well-formed.
How do we translate the (dependent) arrow type in this case?
Well, again there's no other reasonable choice but `Π τ₁ᶜ. τ₂ᶜ`.

Thus what's the type of `μ-ε ε₁δ · (μ-<: <:δ · μ-ε εδ)`?
It's going to be `[ zero ↦ μ-<: <:δ · μ-ε εδ] τ₂ᶜ`.

What's the type of `T-App`? `[ zero ↦τ ε₂ ] τ₂`.
What's its translation?
It can be shown that substitution distributes over translation: `[ zero ↦ ε₂ᶜ ] τ₂ᶜ`,
where `ε₂ᶜ` is `μ-ε ε₂δ`.

And here's the problem: the goal is to show `μ-ε ε₁δ · (μ-<: <:δ · μ-ε εδ) ⦂ [ zero ↦ ε₂ᶜ ] τ₂ᶜ`,
while its type is clearly `μ-ε ε₁δ · (μ-<: <:δ · μ-ε εδ) ⦂ [ zero ↦ <:ᶜ · ε₂ᶜ ] τ₂ᶜ`.

Alas, mismatch. **This won't work.**

What can be done about it?

There are several possibilities.

1. An intermediate language.
2. Computing the return type differently, as opposed to relying on `μ-τ τδ` (unexplored).

### Intermediate

Let's throw up more type systems!

In particular, let's introduce an Intermediate language, having an evidence of subtyping at the syntax level.
Broadly speaking, it'll have another piece of syntax:
```agda
  _S<:_ : (ε : STerm ℓ)
        → (τ : SType ℓ)
        → STerm ℓ
```
where `ε S<: τ` is a syntactic witness that subtyping was used to assign type `τ` to a term `ε`.
This is well-typed iff `Γ ⊢ ε : τ'` and `Γ ⊢ τ' <: τ`:
```agda
  T-SubW : (<:δ : Γ ⊢ τ' <: τ)
         → (εδ : Γ ⊢ ε ⦂ τ')
         → Γ ⊢ ε S<: τ ⦂ τ
```

`T-App` doesn't care about subtyping anymore: it's all delegated to `T-SubW`.

Now we don't have the above problem with goal mismatch in `T-App` translation,
but there is another, subtle but serious problem.
You see, once we add syntactic witnesses of subtyping, narrowing doesn't hold anymore.
What I call the narrowing lemma is that if
```agda
Γ , σ , Δ ⊢ ε ⦂ τ
Γ ⊢ σ' <: σ
```
then
```agda
Γ , σ' , Δ ⊢ ε ⦂ τ
```
and this does hold for the Surface language above (especially if `κ` in its output is existential).

But for the Intermediate language, suppose `ε ~ SVar 0` (so `0`th de Bruijn index) and `Δ` the empty context.
That is, we have
```agda
Γ , σ ⊢ SVar 0 ⦂ σ
Γ ⊢ σ' <: σ
```
Clearly, without implicit subtyping the only thing we can derive about `SVar 0` in `Γ , σ'` is
```agda
Γ , σ' ⊢ SVar 0 ⦂ σ'
```
and there's no way to assign `σ` to `SVar 0` without slapping a `S<:` on top, changing the _syntax_.

Why do we care?
Consider the subtyping relation for arrows:
```agda
  ST-Arr  : (<:₁δ : Γ ⊢ τ₁' <: τ₁)
          → (<:₂δ : Γ , τ₁? ⊢ τ₂' <: τ₂)
          → Γ ⊢ τ₁ ⇒ τ₂' <: τ₁' ⇒ τ₂

```
Here, in the `<:₂δ` premise, should the extended context be `Γ , τ₁` or `Γ , τ₁'`?
If we had narrowing, we could've blindly gone with the former — the latter would've been derivable.
But now we have to actually think, so let's think.

Generally, if we have `Γ ⊢ τ' <: τ`, it's very desirable to have both `Γ ⊢ τ'` and `Γ ⊢ τ`.
I'd even argue that any of these types not being well-formed just does not make sense.

Now, let's apply this reasoning to the conclusion: `Γ ⊢ τ₁ ⇒ τ₂' <: τ₁' ⇒ τ₂`.
We get that both of these should hold:
```agda
Γ ⊢ τ₁ ⇒ τ₂'
Γ ⊢ τ₁' ⇒ τ₂
```
implying that function codomains are well-formed too in the respective contexts:
```agda
Γ , τ₁  ⊢ τ₂'
Γ , τ₁' ⊢ τ₂
```

Now let's apply this very reasoning to the `<:₂δ` premise.
It should _also_ hold that
```agda
Γ , τ₁? ⊢ τ₂'
Γ , τ₁? ⊢ τ₂
```

Now, should `τ₁?` be `τ₁` or `τ₁'`? Let's consider both cases.

1. `τ₁? ~ τ₁`. Then we shall have simultaneously
   ```agda
   Γ , τ₁' ⊢ τ₂
   Γ , τ₁  ⊢ τ₂
   ```
2. `τ₁? ~ τ₁'`. Then we shall have simultaneously
   ```agda
   Γ , τ₁  ⊢ τ₂'
   Γ , τ₁' ⊢ τ₂'
   ```

Either way, either `τ₂` or `τ₂'` shall be well-formed in contexts with both `τ₁` and `τ₁'` at the top.
Again, if we have narrowing, that's no big deal — one implies the other.

But, if we don't, and if the witness is syntactic,
the only way this can work is if the result of the function (`τ₂` or `τ₂'`)
doesn't depend on its argument (`τ₁`, primed or not).
(More precisely, there are still forms of dependencies that are allowed,
but they are much more limited now, and it's not obvious what the proper restriction is.)
But we certainly want to allow the dependency!

**This won't work.**

#### How can this be fixed?

1. Somehow slap `S<:` into `T-App` (unexplored).
2. Don't have subtyping on function types (unexplored).

What can we say about these?

For the first one, I have a gut feel it won't work.
In particular, we might have something like, in surface language
```idris
f : {ν : Int | ν > 0} → {ν : Int | ν > 0}
f x = x

case f 5 of ...
```
which gets desugared to
```idris
case f (5 S<: {ν : Int | ν > 0}) of ...
```
which gets evaluated to
```idris
case 5 S<: {ν : Int | ν > 0} of ...
```
and we need to be able to type `5 S<: {ν : Int | ν > 0}` irrespective of whether it's a function argument.
There are probably ways to thread this through intro/elim pairs, but it gets hairy really soon.

On the other hand, we might take middle ground.
We might both allow having `_S<:_` anywhere, as well as _require_ it to be present in function applications
(where subtyping actually makes a difference).
In this case, some form of narrowing might hold.
Or it might not, it's still hairy.

The second point is also worth a couple extra words.
Indeed, our refinement types happen only on base types, and we emulate refinements on functions via dummy arguments.
Moreover, the subtyping relation on function types is derived from the subtyping of individual non-functional values.
Thus, when translating from Surface to Intermediate,
we can translate the subtyping witness on the individual (non-function) values into the right syntactic thing,
and then translate the subtyping on functions by η-expanding everything and applying the syntactic witness to the 
function arguments.

In a sense, we don't need a separate subtyping relation in the intermediate language at all.
