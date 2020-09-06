module Surface.Theorems.Thinning

import Data.Fin
import Data.List
import Data.Vect
import Data.Vect.Quantifiers

import Surface.Syntax
import Surface.Derivations
import Surface.Theorems.Lemmas
import Surface.Theorems.TCTX

import Helpers

%default total

mutual
  export
  twfThinning : Sublist g g' -> ok g' -> (g |- t) -> (g' |- t)
  twfThinning _      g'ok (TWF_TrueRef g') = TWF_TrueRef g'ok
  twfThinning subPrf g'ok (TWF_Base t1 t2) = let expCtxOk = TCTX_Bind g'ok (TWF_TrueRef g'ok)
                                              in TWF_Base (tThinning (AppendBoth subPrf) expCtxOk t1) (tThinning (AppendBoth subPrf) expCtxOk t2)
  twfThinning subPrf g'ok (TWF_Conj twfr1 twfr2) = TWF_Conj (twfThinning subPrf g'ok twfr1) (twfThinning subPrf g'ok twfr2)
  twfThinning subPrf g'ok (TWF_Arr twf1 twf2) = TWF_Arr
                                                  (twfThinning subPrf g'ok twf1)
                                                  (twfThinning (AppendBoth subPrf) (TCTX_Bind g'ok (twfThinning subPrf g'ok twf1)) twf2)
  twfThinning subPrf g'ok (TWF_ADT preds) = TWF_ADT (thinAll preds)
    where
      thinAll : All (\t => g |- t) ls -> All (\t => g' |- t) ls
      thinAll [] = []
      thinAll (a :: as) = twfThinning subPrf g'ok a :: thinAll as

  export
  tThinning : {e : STerm} -> Sublist g g' -> ok g' -> (g |- e :. t) -> (g' |- e :. t)
  tThinning subPrf g'ok (T_Unit gokPrf) = T_Unit g'ok
  tThinning subPrf g'ok (T_Var _ elemPrf) = T_Var g'ok (superListHasElems subPrf elemPrf)
  tThinning subPrf g'ok (T_Abs arrWfPrf body) = let arrWfPrf' = twfThinning subPrf g'ok arrWfPrf
                                                    body'ctx = TCTX_Bind g'ok (arrWfImpliesDomWf arrWfPrf')
                                                    body' = tThinning (AppendBoth subPrf) body'ctx body
                                                 in T_Abs arrWfPrf' body'
  tThinning subPrf g'ok (T_App t1 t2) = T_App (tThinning subPrf g'ok t1) (tThinning subPrf g'ok t2)
  tThinning subPrf g'ok (T_Case twf scrut branches) = T_Case (twfThinning subPrf g'ok twf) (tThinning subPrf g'ok scrut) (thinBranches branches)
    where
      thinBranches : BranchesHaveType g cons bs t -> BranchesHaveType g' cons bs t
      thinBranches NoBranches = NoBranches
      thinBranches (OneMoreBranch eprf rest) =
        case T_implies_TCTX eprf of
             TCTX_Bind prevOk tyPrf => let conTyOk = twfThinning subPrf g'ok $ assert_smaller (OneMoreBranch eprf rest) tyPrf
                                        in OneMoreBranch (tThinning (AppendBoth subPrf) (TCTX_Bind g'ok conTyOk) eprf) (thinBranches rest)
  tThinning subPrf g'ok (T_Con arg adtTy) = T_Con (tThinning subPrf g'ok arg) (twfThinning subPrf g'ok adtTy)
  tThinning subPrf g'ok (T_Sub x y) = ?thinning_sub_hole

export
twfWeaken : {g : Ctx} -> (ok g) -> (g |- ht) -> (g |- t) -> ((_, ht) :: g |- t)
twfWeaken {g} gok htPrf tPrf = twfThinning (IgnoreHead $ sublistSelf g) (TCTX_Bind gok htPrf) tPrf

export
tWeaken : {g : Ctx} -> {e : STerm} -> (ok g) -> (g |- ht) -> (g |- e :. t) -> ((_, ht) :: g |- e :. t)
tWeaken {g} gok htPrf tPrf = tThinning (IgnoreHead $ sublistSelf g) (TCTX_Bind gok htPrf) tPrf
