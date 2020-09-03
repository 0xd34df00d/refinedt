module Surface.Theorems.Lemmas

import Surface.Syntax
import Surface.Derivations

%default total

export
arrWfImpliesDomWf : (g |- SArr x t1 t2) -> (g |- t1)
arrWfImpliesDomWf (TWF_Arr dom _) = dom

export
arrWfImpliesCodWf : (g |- SArr x t1 t2) -> (((x, t1) :: g) |- t2)
arrWfImpliesCodWf (TWF_Arr _ cod) = cod

export
tossMidElem : (front : List a) -> (mid : a) -> (back : List a)
           -> ((front ++ [mid]) ++ back) = (front ++ mid :: back)
tossMidElem [] mid back = Refl
tossMidElem (_ :: front') mid back = rewrite tossMidElem front' mid back in Refl

export
tossTWF : ((d ++ [p1]) ++ p2 :: g |- t)
       -> (d ++ p1 :: p2 :: g |- t)
tossTWF {d} {p1} {p2} {g} prf = rewrite sym $ tossMidElem d p1 (p2 :: g) in prf
