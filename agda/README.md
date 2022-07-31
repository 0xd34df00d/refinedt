# Structure

* `Surface/` contains the formalization of the surface language,
  including its syntax as well as the declarative and algorithmic type systems.
  In particular, the two most important theorems, Progress and Preservation, are proven for the
  [declarative](Surface/Derivations/Declarative/Theorems/Safety.agda) and [algorithmic](Surface/Derivations/Algorithmic/Theorems/Safety.agda)
  type systems.
* `Intermediate/` contains the formalization of the intermediate language,
  which is effectively surface language with some extra syntax and typings for making subtyping explicit.
  It's also basically a copypasta of `Surface/` with minor changes to account for those extra things.
  Eventually, it'll either be merged with `Surface/`, or `Surface/` will be reduced considerably.
* `Core/` contains the formalization of the core language.
  Since we build on the existing and well-known CoC-style type system, we do not prove its metatheoretical properties.

## Warning

Not all modules are buildable/type-checkable at all times.
As the project evolves, some changes to the syntax, the type systems or the lemmas might break some of the modules.
Eventually everything will compile, though. Eventually.
