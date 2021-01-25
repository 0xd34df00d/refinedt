# Structure

* `Surface/` contains the formalization of the surface language.
  In particular, the two most important theorems, Progress and Preservation, are proven in the [Surface.Safety](Surface/Safety.agda) module.
* `Core/` contains the formalization of the surface language.
  Since we build on the existing and well-known CoC-style type system, we do not prove its metatheoretical properties.
* `Translation/` will contain the definition of the translation between the two along with proofs of correctness.
