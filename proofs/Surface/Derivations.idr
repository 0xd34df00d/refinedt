module Surface.Derivations

import Surface.Syntax

%default total
%access public export

syntax [γ] "ok" = TCTX γ
syntax [γ] "|-" [τ] = TWF γ τ 
syntax [y] "|-" [ε] ":" [τ] = T γ ε τ

mutual
  data TCTX : (γ : Context) -> Type where
    TCTX_Empty  : TCTX Empty
    TCTX_Bind   : TCTX γ -> (γ |- τ) -> TCTX ((var, τ) :: γ)

  data TWF : (γ : Context) -> (τ : SType) -> Type where
