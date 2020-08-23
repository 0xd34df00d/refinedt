module Surface.Derivations

import Data.List
import Data.So
import Data.Vect
import Data.Vect.Quantifiers

import Surface.Syntax

%default total

syntax [g] "ok" = TCTX g
syntax [h] "|-" [t] = TWF h t
syntax [g] "|-" [e] ":" [t] = T g e t
syntax [g] "|-" [t] "<:" [t'] = ST g t t'

public export
record Oracle where
  constructor MkOracle
  decide : (var : Var) -> (b : BaseType) -> (r1 : Refinement) -> (r2 : Refinement) -> Maybe () -- TODO refine the return type

mutual
  public export
  data TCTX : (g : Ctx) -> Type where
    TCTX_Empty  : TCTX []
    TCTX_Bind   : TCTX g -> (g |- t) -> TCTX ((var, t) :: g)

  public export
  data TWF : (g : Ctx) -> (t : SType) -> Type where
    TWF_TrueRef : g ok
               -> g |- { v : b | Τ }
    TWF_Base    : (((v, { v1 : b | Τ }) :: g) |- e1 : { v2 : b' | Τ })
               -> (((v, { v1 : b | Τ }) :: g) |- e2 : { v2 : b' | Τ })
               -> (g |- { v : b | e1 |=| e2 })
    TWF_Conj    : (g |- { v : b | r1 })
               -> (g |- { v : b | r2 })
               -> (g |- { v : b | r1 & r2 })
    TWF_Arr     : (g |- t1)
               -> (((x, t1) :: g) |- t2)
               -> (g |- SArr x t1 t2)
    TWF_ADT     : All (\conTy => g |- conTy) adtCons
               -> (g |- SADT adtCons)

  public export
  data BranchesHaveType : (cons : ADTCons n) -> (branches : CaseBranches n) -> (t' : SType) -> Type where
    NoBranches    : BranchesHaveType [] [] t'
    OneMoreBranch : {conTy : SType} -> {var : Var} -> {body : STerm}
                 -> (((var, conTy) :: g) |- body : t')         -- TODO x fresh name in context?
                 -> (rest : BranchesHaveType cons branches t')
                 -> BranchesHaveType (conTy :: cons) (MkCaseBranch var body :: branches) t'

  public export
  data T : (g : Ctx) -> (e : STerm) -> (t : SType) -> Type where
    T_Unit      : g ok
               -> g |- SUnit : { v : BUnit | Τ }
    T_Var       : g ok
               -> Elem (x, t) g
               -> (g |- (SVar x) : t)
    T_Abs       : (g |- SArr x t1 t2)
               -> (((x, t1) :: g) |- e : t2)
               -> (g |- (SLam x t1 e) : SArr x t1 t2)
    T_App       : (g |- e1 : SArr x t1 t2)
               -> (g |- e2 : t1)
               -> (g |- (SApp e1 e2) : substInType x e2 t2)
    T_Case      : (g |- t')
               -> (g |- e : SADT cons)
               -> BranchesHaveType cons branches t'
               -> (g |- (SCase e branches) : t')
    T_Con       : (g |- e : tj)
               -> (g |- SADT cons)
               -> (g |- (SCon idx e cons) : SADT cons)
    T_Sub       : (g |- e : t)
               -> (g |- t <: t')
               -> (g |- e : t')

  public export
  data ST : (g : Ctx) -> (t1 : SType) -> (t2 : SType) -> Type where
    ST_Base     : (oracle : Oracle)
               -> So (isJust (decide oracle v b r1 r2))
               -> (g |- { v : b | r1 } <: { v : b | r2 })
    ST_Arr      : (g |- t1' <: t1)
               -> (((x, t1') :: g) |- t2 <: t2')
               -> (g |- (SArr x t1 t2) <: (SArr x t1' t2'))
