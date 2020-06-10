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
