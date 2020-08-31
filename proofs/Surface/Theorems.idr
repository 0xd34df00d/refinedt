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

%default total

-- Well-typedness of a term in a context implies well-formedness of said context
T_implies_TCTX : {e : STerm} -> (g |- e :. t) -> ok g
T_implies_TCTX (T_Unit gok) = gok
T_implies_TCTX (T_Var gok _) = gok
T_implies_TCTX (T_Abs _ bodyPrf) = case T_implies_TCTX bodyPrf of
                                        TCTX_Bind gok _ => gok
T_implies_TCTX (T_App arrWfPrf _) = T_implies_TCTX arrWfPrf
T_implies_TCTX (T_Case _ consPrf _) = T_implies_TCTX consPrf
T_implies_TCTX (T_Con eprf _) = T_implies_TCTX eprf
T_implies_TCTX (T_Sub eprf _) = T_implies_TCTX eprf


-- Well-formedness of a type in a context implies well-formedness of said context
TWF_implies_TCTX : (g |- t) -> ok g
TWF_implies_TCTX (TWF_TrueRef gok) = gok
TWF_implies_TCTX (TWF_Base t1 _) = case T_implies_TCTX t1 of
                                         TCTX_Bind gok _ => gok
TWF_implies_TCTX (TWF_Conj twfr1 _) = TWF_implies_TCTX twfr1
TWF_implies_TCTX (TWF_Arr twft1 _) = TWF_implies_TCTX twft1
TWF_implies_TCTX (TWF_ADT (con1Ty :: _)) = TWF_implies_TCTX con1Ty


twfWeaken : {g : Ctx} -> (ok g) -> (g |- ht) -> (g |- t) -> ((_, ht) :: g |- t)
twfWeaken {g} gok htPrf tPrf = twfThinning (IgnoreHead $ sublistSelf g) (TCTX_Bind gok htPrf) tPrf

tWeaken : {g : Ctx} -> {e : STerm} -> (ok g) -> (g |- ht) -> (g |- e :. t) -> ((_, ht) :: g |- e :. t)
tWeaken {g} gok htPrf tPrf = tThinning (IgnoreHead $ sublistSelf g) (TCTX_Bind gok htPrf) tPrf

substInCtx : Var -> STerm -> Ctx -> Ctx
substInCtx x e [] = []
substInCtx x e ((x', ty) :: rest) = (x', substInType x e ty) :: substInCtx x e rest

substInCtxSnoc : (x, e, y, t, g : _)
              -> substInCtx x e (g ++ [(y, t)]) = substInCtx x e g ++ [(y, substInType x e t)]
substInCtxSnoc _ _ _ _ [] = Refl
substInCtxSnoc x e y t ((_, _) :: g') = rewrite substInCtxSnoc x e y t g' in Refl

tossMidElem : (front : List a) -> (mid : a) -> (back : List a)
           -> ((front ++ [mid]) ++ back) = (front ++ mid :: back)
tossMidElem [] mid back = Refl
tossMidElem (_ :: front') mid back = rewrite tossMidElem front' mid back in Refl

tossTWF : ((d ++ [p1]) ++ p2 :: g |- t)
       -> (d ++ p1 :: p2 :: g |- t)
tossTWF {d} {p1} {p2} {g} prf = rewrite sym $ tossMidElem d p1 (p2 :: g) in prf

-- g is for Γ
-- d is for Δ
mutual
  derivesSubstituted : (g |- e :. s)
                    -> (d ++ (x, s) :: g |- tau)
                    -> (d ++ (x, s) :: g |- substInType x e tau)

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
  singleSubstInCtxTWF eprf (TWF_Base e1deriv e2deriv) = TWF_Base ?w1 ?w2
  singleSubstInCtxTWF eprf (TWF_Conj r1deriv r2deriv) = TWF_Conj (singleSubstInCtxTWF eprf r1deriv) (singleSubstInCtxTWF eprf r2deriv)
  singleSubstInCtxTWF eprf (TWF_Arr argTy bodyTy) = TWF_Arr (singleSubstInCtxTWF eprf argTy) ?w4 -- (singleSubstInCtxTWF eprf bodyTy)
  singleSubstInCtxTWF eprf (TWF_ADT cons) = TWF_ADT $ substCons eprf cons
    where
      substCons : {x, t, y, d : _}
               -> (g |- e :. s)
               -> All (\ty => (d ++ (y, t) :: (x, s) :: g) |- ty) tys
               -> All (\ty => (d ++ (y, substInType x e t) :: (x, s) :: g) |- ty) tys
      substCons _ [] = []
      substCons eprf (a :: as) = singleSubstInCtxTWF eprf a :: substCons eprf as

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
  exchangeTWF no_x (TWF_Base e1deriv e2deriv) = TWF_Base ?e1 ?e2
  exchangeTWF no_x (TWF_Conj r1deriv r2deriv) = TWF_Conj (exchangeTWF no_x r1deriv) (exchangeTWF no_x r2deriv)
  exchangeTWF no_x (TWF_Arr w v) = ?exchange_rhs_4
  exchangeTWF no_x (TWF_ADT w) = TWF_ADT ?e5

  substPreservesTWF : {x, e, g : _}
                   -> (g |- e :. s)
                   -> (d ++ (x, s) :: g |- tau)
                   -> SnocList d
                   -> (substInCtx x e d ++ g |- substInType x e tau)
  substPreservesTWF eprf tauprf Empty = substPreservesTWFHead eprf tauprf
  substPreservesTWF eprf tauprf (Snoc (y, t) d init) =
    let tWellFormed = strip_d d tauprf
        tauprf' = exchangeTWF ?t_no_x' $ singleSubstInCtxTWF eprf $ tossTWF tauprf
        tsubst_ok_in_g = substPreservesTWFHead eprf tWellFormed
        rec = substPreservesTWF (tWeaken (T_implies_TCTX eprf) tsubst_ok_in_g eprf) tauprf' init
     in rewrite substInCtxSnoc x e y t d
     in rewrite tossMidElem (substInCtx x e d) (y, substInType x e t) g
     in rec
    where
      strip_d : (d : Ctx) -> (((d ++ [(_, t)]) ++ (x, s) :: g) |- _) -> ((x, s) :: g |- t)
      strip_d [] prf = case TWF_implies_TCTX prf of
                            TCTX_Bind _ tPrf => tPrf
      strip_d (d :: ds) prf = case TWF_implies_TCTX prf of
                                   TCTX_Bind _ tPrf => strip_d ds tPrf

  substPreservesTWFHead : {x, e, g : _}
                       -> (g |- e :. s) -> (((x, s) :: g) |- tau)
                       -> (g |- substInType x e tau)
  substPreservesTWFHead eprf (TWF_TrueRef (TCTX_Bind gok _)) = TWF_TrueRef gok
  substPreservesTWFHead eprf (TWF_Base e1deriv e2deriv) = TWF_Base ?y1 ?y2
  substPreservesTWFHead eprf (TWF_Conj r1deriv r2deriv) = TWF_Conj (substPreservesTWFHead eprf r1deriv) (substPreservesTWFHead eprf r2deriv)
  substPreservesTWFHead eprf (TWF_Arr t1prf t2prf) =
    let t1prf' = substPreservesTWFHead eprf t1prf
        t2prf' = substPreservesTWF eprf t2prf (snocList [_])
     in TWF_Arr t1prf' t2prf'
  substPreservesTWFHead eprf (TWF_ADT alls) = TWF_ADT $ substPreservesCons eprf alls
    where
      substPreservesCons : (g |- e :. t1)
                        -> All (\conTy => (x, t1) :: g |- conTy) cons
                        -> All (\conTy => g |- conTy) (substInADT x e cons)
      substPreservesCons _ [] = []
      substPreservesCons eprf (con :: cons) = substPreservesTWFHead eprf con :: substPreservesCons eprf cons

-- Well-typedness of a term in a context implies well-formedness of its type in said context
T_implies_TWF : {e : STerm} -> {g : _} -> (g |- e :. t) -> (g |- t)
T_implies_TWF (T_Unit gok) = TWF_TrueRef gok
T_implies_TWF (T_Var gok elemPrf) = anyTypeInCtxIsWellformed gok elemPrf
  where
    anyTypeInCtxIsWellformed : {g : _} -> (ok g) -> Elem (x, t) g -> (g |- t)
    anyTypeInCtxIsWellformed (TCTX_Bind init twfPrf) Here = twfWeaken init twfPrf twfPrf
    anyTypeInCtxIsWellformed (TCTX_Bind init twfPrf) (There later) = twfWeaken init twfPrf $ anyTypeInCtxIsWellformed init later
T_implies_TWF (T_Abs arrWfPrf _) = arrWfPrf
T_implies_TWF (T_App prf1 prf2) = substPreservesTWFHead prf2 (arrWfImpliesCodWf $ T_implies_TWF prf1)
T_implies_TWF (T_Case wfPrf _ _) = wfPrf
T_implies_TWF (T_Con _ wfPrf) = wfPrf
T_implies_TWF (T_Sub x y) = ?T_implies_TWF_sub_hole
