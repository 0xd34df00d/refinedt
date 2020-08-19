module Surface.Derivations

import Data.List.Quantifiers

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
    TWF_TrueRef : γ |- { v : b | Τ }
    TWF_Base    : (((v, { v : b1 | Τ }) :: γ) |- ε1 : { v2 : b' | Τ })
               -> (((v, { v : b1 | Τ }) :: γ) |- ε2 : { v2 : b' | Τ })
               -> (γ |- { v : b | ε1 |=| ε2 })
    TWF_Conj    : (γ |- { v : b | r1 })
               -> (γ |- { v : b | r2 })
               -> (γ |- { v : b | r1 & r2 })
    TWF_Arr     : (γ |- τ1)
               -> (((x, τ1) :: γ) |- τ2)
               -> (γ |- SArr x τ1 τ2)
    TWF_ADT     : All (\(_, conTy) => γ |- conTy) adtCons
               -> (γ |- SADT adtCons)

  data T : (γ : Context) -> (ε : STerm) -> (τ : SType) -> Type where
