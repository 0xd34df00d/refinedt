module Surface.Derivations

import Data.List
import Data.Vect
import Data.Vect.Quantifiers

import Surface.Syntax

%default total
%access public export

syntax [g] "ok" = TCTX g
syntax [g] "|-" [t] = TWF g t
syntax [g] "|-" [e] ":" [t] = T g e t

mutual
  data TCTX : (g : Ctx) -> Type where
    TCTX_Empty  : TCTX Empty
    TCTX_Bind   : TCTX g -> (g |- t) -> TCTX ((var, t) :: g)

  data TWF : (g : Ctx) -> (t : SType) -> Type where
    TWF_TrueRef : g |- { v : b | Τ }
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

  data BranchesHaveType : (cons : ADTCons n) -> (branches : CaseBranches n) -> (t' : SType) -> Type where
    NoBranches    : BranchesHaveType [] [] t'
    OneMoreBranch : {conTy : SType} -> {var : Var} -> {body : STerm}
                 -> (((var, conTy) :: g) |- body : t')         -- TODO x fresh name in context?
                 -> (rest : BranchesHaveType cons branches t')
                 -> BranchesHaveType (conTy :: cons) (MkCaseBranch var body :: branches) t'

  data T : (g : Ctx) -> (e : STerm) -> (t : SType) -> Type where
    T_Unit      : g |- SUnit : { v : BUnit | Τ }
    T_Var       : Elem (x, t) (bindings g)
               -> (g |- (SVar x) : t)
    T_Abs       : (((x, t1) :: g) |- e : t2)   -- TODO do we really need the arrow TWF premise?
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

  data ST : (g : Ctx) -> (t1 : SType) -> (t2 : SType) -> Type where
