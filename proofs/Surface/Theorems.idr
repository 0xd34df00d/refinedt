module Surface.Theorems

import Data.Fin
import Data.List
import Data.List.Elem
import Data.List.Views
import Data.Vect
import Data.Vect.Quantifiers

import Surface.Syntax
import Surface.Derivations

import Helpers

import Surface.Theorems.Lemmas
import Surface.Theorems.Thinning
import Surface.Theorems.TCTX

%default total

mutual
  exchangeTCTX : {g, d : _}
              -> (g |- t)
              -> ok (d ++ (y, t) :: (x, s) :: g)
              -> ok (d ++ (x, s) :: (y, t) :: g)
  exchangeTCTX {d = []} no_x (TCTX_Bind (TCTX_Bind prevOk tyPrf') tyPrf) = TCTX_Bind (TCTX_Bind prevOk no_x) (twfWeaken prevOk no_x tyPrf')
  exchangeTCTX {d = (hx, ht) :: d} no_x (TCTX_Bind prevOk tyPrf) = TCTX_Bind (exchangeTCTX no_x prevOk) (exchangeTWF no_x tyPrf)

  exchangeTWF : {g, d : _}
             -> (g |- t)
             -> ((d ++ (y, t) :: (x, s) :: g) |- tau)
             -> ((d ++ (x, s) :: (y, t) :: g) |- tau)
  exchangeTWF no_x (TWF_TrueRef gok) = TWF_TrueRef (exchangeTCTX no_x gok)
  exchangeTWF no_x (TWF_Base e1deriv e2deriv) = TWF_Base ?later ?later
  exchangeTWF no_x (TWF_Conj r1deriv r2deriv) = TWF_Conj (exchangeTWF no_x r1deriv) (exchangeTWF no_x r2deriv)
  exchangeTWF {d} no_x (TWF_Arr {x} {t1} argTy bodyTy) = TWF_Arr (exchangeTWF no_x argTy) (exchangeTWF {d = (x, t1) :: d} no_x bodyTy)
  exchangeTWF no_x (TWF_ADT cons) = TWF_ADT $ exchangeCons cons
    where
      exchangeCons : All (\conTy => (d ++ ((y, t) :: (x, s) :: g)) |- conTy) adtCons
                  -> All (\conTy => (d ++ ((x, s) :: (y, t) :: g)) |- conTy) adtCons
      exchangeCons [] = []
      exchangeCons (a :: as) = exchangeTWF no_x a :: exchangeCons as


-- g is for Γ
-- d is for Δ
mutual
  singleSubstInCtxTCTX : {g, d, x, y, t, e : _}
                      -> (g |- e :. s)
                      -> ok (d ++ (y, t) :: (x, s) :: g)
                      -> ok (d ++ (y, substInType x e t) :: (x, s) :: g)
  singleSubstInCtxTCTX {d = []} eprf (TCTX_Bind prevOk@(TCTX_Bind prevOk' tyPrf') tyPrf) =
    TCTX_Bind prevOk (twfWeaken prevOk' tyPrf' $ substPreservesTWFHead eprf tyPrf)
  singleSubstInCtxTCTX {d = (dx, dt) :: d} eprf (TCTX_Bind prevOk tyPrf) =
    TCTX_Bind (singleSubstInCtxTCTX eprf prevOk) (singleSubstInCtxTWF eprf tyPrf)

  singleSubstInCtxTWF : {x, y, t, g, d, e : _}
                     -> (g |- e :. s)
                     -> ((d ++ (y, t) :: (x, s) :: g) |- tau)
                     -> ((d ++ (y, substInType x e t) :: (x, s) :: g) |- tau)
  singleSubstInCtxTWF eprf (TWF_TrueRef gok) = TWF_TrueRef $ singleSubstInCtxTCTX eprf gok
  singleSubstInCtxTWF eprf (TWF_Base e1deriv e2deriv) = TWF_Base ?later ?later
  singleSubstInCtxTWF eprf (TWF_Conj r1deriv r2deriv) = TWF_Conj (singleSubstInCtxTWF eprf r1deriv) (singleSubstInCtxTWF eprf r2deriv)
  singleSubstInCtxTWF {d} eprf (TWF_Arr {x} {t1} argTy bodyTy) = TWF_Arr (singleSubstInCtxTWF eprf argTy) (singleSubstInCtxTWF {d = (x, t1) :: d} eprf bodyTy)
  singleSubstInCtxTWF eprf (TWF_ADT cons) = TWF_ADT $ substCons cons
    where
      substCons : {x, t, y, d : _}
               -> All (\ty => (d ++ (y, t) :: (x, s) :: g) |- ty) tys
               -> All (\ty => (d ++ (y, substInType x e t) :: (x, s) :: g) |- ty) tys
      substCons [] = []
      substCons (a :: as) = singleSubstInCtxTWF eprf a :: substCons as

  substPreservesTWF : {x, e, g : _}
                   -> (g |- e :. s)
                   -> (d ++ (x, s) :: g |- tau)
                   -> SnocList d
                   -> (substInCtx x e d ++ g |- substInType x e tau)
  substPreservesTWF eprf tauprf Empty = substPreservesTWFHead eprf tauprf
  substPreservesTWF eprf tauprf (Snoc (y, t) d init) =
    let tWellFormed = midCtxTWF d tauprf
        no_x_prf = substPreservesTWFHead eprf tWellFormed
        tauprf' = exchangeTWF no_x_prf $ singleSubstInCtxTWF eprf $ tossTWF tauprf
        tsubst_ok_in_g = substPreservesTWFHead eprf tWellFormed
        rec = substPreservesTWF (tWeaken (T_implies_TCTX eprf) tsubst_ok_in_g eprf) tauprf' init
     in rewrite substInCtxSnoc x e y t d
     in rewrite tossMidElem (substInCtx x e d) (y, substInType x e t) g
     in rec

  substPreservesTWFHead : {x, e, g : _}
                       -> (g |- e :. s)
                       -> ((x, s) :: g |- tau)
                       -> (g |- substInType x e tau)
  substPreservesTWFHead eprf (TWF_TrueRef (TCTX_Bind gok _)) = TWF_TrueRef gok
  substPreservesTWFHead eprf (TWF_Base e1deriv e2deriv) = TWF_Base ?later ?later
  substPreservesTWFHead eprf (TWF_Conj r1deriv r2deriv) = TWF_Conj (substPreservesTWFHead eprf r1deriv) (substPreservesTWFHead eprf r2deriv)
  substPreservesTWFHead eprf (TWF_Arr t1prf t2prf) =
    let t1prf' = substPreservesTWFHead eprf t1prf
        t2prf' = substPreservesTWF eprf t2prf (snocList [_])
     in TWF_Arr t1prf' t2prf'
  substPreservesTWFHead eprf (TWF_ADT alls) = TWF_ADT $ substPreservesCons alls
    where
      substPreservesCons : All (\conTy => (x, s) :: g |- conTy) cons
                        -> All (\conTy => g |- conTy) (substInADT x e cons)
      substPreservesCons [] = []
      substPreservesCons (con :: cons) = substPreservesTWFHead eprf con :: substPreservesCons cons

-- Well-typedness of a term in a context implies well-formedness of its type in said context
T_implies_TWF : {e : STerm} -> {g : _} -> (g |- e :. t) -> (g |- t)
T_implies_TWF (T_Unit gok) = TWF_TrueRef gok
T_implies_TWF (T_Var gok elemPrf) = anyTypeInCtxIsWellformed gok elemPrf
T_implies_TWF (T_Abs arrWfPrf _) = arrWfPrf
T_implies_TWF (T_App prf1 prf2) = substPreservesTWFHead prf2 (arrWfImpliesCodWf $ T_implies_TWF prf1)
T_implies_TWF (T_Case wfPrf _ _) = wfPrf
T_implies_TWF (T_Con _ wfPrf) = wfPrf
T_implies_TWF (T_Sub x y) = ?T_implies_TWF_sub_hole
