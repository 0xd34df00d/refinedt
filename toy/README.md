# toy

## Building and running

You'll need Idris to run most of this.

### OS X caveats

If z3 isn't installed in a location like `/usr` or `/usr/local`, then `stack`/`cabal` will have trouble finding it.
To fix, assuming it's in `/Users/foo/local`:

1. Add these into your `~/.stack/config.yaml`:
```yaml
extra-include-dirs:
- /Users/foo/local/include
extra-lib-dirs:
- /Users/foo/local/lib
```

2. Symlink the library into a standard path: `sudo ln -s ~/local/lib/libz3.dylib /usr/local/lib`

## Syntax

The toy language is largely a tiny subset of Idris with a bit of extra syntax for the refinements.
Refined types are written in curly braces: `{ v : Int | v >= 0 & v < x }` as an example.

### A few more examples

Path sensitivity and dependent refinements:
```idris
max : (x : Int) -> (y : Int) -> { v : Int | v >= x & v >= y }
max x y = if x > y then y else x
```

Subtyping and co/contravariance for function arguments:
```idris
f : (x : { v : Int | v >= 0 })
 -> (y : { v : Int | v >= 0 })
 -> { v : Int | v > 0 }

g : ((x : { v : Int | v > 0 }) -> (y : { v : Int | v > 0 }) -> { v : Int | v >= 0 })
 -> { v : Int | v >= 0 }

h : { v : Int | v >= 0 }
h = g f
```

### (Semi-)formal syntax

The syntax can be reasonably approximated by the following grammar,
`prog` being the start nonterminal:

```ebnf
prog := {decl} EOF;

decl := funSig [funDef];

(* Fun signatures and types *)
funSig := funName ":" type EOL {EOL};

type := arrow
      | arrowLHS;
arrow := (boundLHS | arrowLHS) "->" type;
boundLHS := "(" binder ":" type ")";
arrowLHS := "(" arrow ")"
          | baseRT;
baseRT := baseTy
        | "{ v :" baseTy "|" refinement "}";
baseTy := "Int" | "Bool" | "IntList";

refinement := atomicRefinement {"&" atomicRefinement};
atomicRefinement := "v" op arg;
op := "<=" | "<" | "=" | "/=" | ">=" | ">";
arg := decimal | "len" identifier | identifier;

(* Fun definitions and terms *)
funDef := funName binder* "=" term EOL {EOL};

term := tapps
      | term binOp term;
tapps := atom {atom};
atom := identifier
      | decimal
      | "if" term "then" term "else" term
      | "(" term ")";
binOp := "+" | "-" | ">" | "<";

funName := identifier;
binder := identifier;

identifier := letter {alphaNum | "'"};
```

Here,
* `EOF`, `EOL` have the obvious meaning.
* `letter` is a Unicode letter as in `Data.Char.isLetter`.
* Similarly, `alphaNum` is whatever `Data.Char.isAlphaNum` accepts.
* `decimal` is a decimal integer.

The most interesting parsers are defined in the following files:
* [Types parser](src/Toy/Language/Parser/Ty.hs)
* [Terms parser](src/Toy/Language/Parser/Decl.hs)

#### Caveats

* The `funDef` following a `funSig` is expected (and checked) to have the same `funName` as the `funSig`.
* The `binder`s in `funSig` (in `boundLHS`) are expected (and _not checked_) to have the same name
  as the matching `binder`s in `funDef`: that is, the following is bad:
  ```idris
  foo : (x : Int) -> Int
  foo y = y
  ```
  Here `x` should be changed to `y` or vice versa.

  Of course, this doesn't matter for those arguments that aren't bound in the type:
  ```idris
  foo : (x : Int) -> Int -> Int
  foo x arg2 = x + arg2
  ```
  Here `arg2` can be renamed arbitrarily.
* Shadowing variable names isn't checked, let alone dealt with.
