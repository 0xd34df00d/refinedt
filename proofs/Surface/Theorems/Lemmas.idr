module Surface.Theorems.Lemmas

import Surface.Syntax
import Surface.Derivations

%default total

export
arrWfImpliesDomWf : (g |- SArr x t1 t2) -> (g |- t1)
arrWfImpliesDomWf (TWF_Arr dom _) = dom
