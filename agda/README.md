# Structure

* `Surface/` contains the formalization of the surface language.
  In particular, the two most important theorems, Progress and Preservation, are proven in the [Surface.Safety](Surface/Safety.agda) module.
* `Intermediate/` contains the formalization of the intermediate language,
  which is basically surface language with some extra syntax and typings for making subtyping explicit.
  It's also basically a copypasta of `Surface/` with minor changes to account for those extra things.
  Eventually, it'll either be merged with `Surface/`, or `Surface/` will be reduced considerably.
* `Core/` contains the formalization of the core language.
  Since we build on the existing and well-known CoC-style type system, we do not prove its metatheoretical properties.
* `Translation/` will contain the definition of the translation between the two along with proofs of correctness.
