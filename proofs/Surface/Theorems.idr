module Surface.Theorems

import Data.Fin
import Data.List
import Data.List.Views
import Data.Vect
import Data.Vect.Quantifiers

import Surface.Syntax
import Surface.Derivations

import Helpers

import Surface.Theorems.Lemmas
import Surface.Theorems.Thinning

%default total

T_implies_TCTX : (g |- e : t) -> g ok
T_implies_TCTX (T_Unit gok) = gok
T_implies_TCTX (T_Var gok _) = gok
T_implies_TCTX (T_Abs _ bodyPrf) = case T_implies_TCTX bodyPrf of
                                        TCTX_Bind gok _ => gok
T_implies_TCTX (T_App arrWfPrf _) = T_implies_TCTX arrWfPrf
T_implies_TCTX (T_Case _ consPrf _) = T_implies_TCTX consPrf
T_implies_TCTX (T_Con eprf _) = T_implies_TCTX eprf
T_implies_TCTX (T_Sub eprf _) = T_implies_TCTX eprf


twfWeaken : (g ok) -> (g |- ht) -> (g |- t) -> (((_, ht) :: g) |- t)
twfWeaken {g} gok htPrf tPrf = twfThinning (IgnoreHead $ sublistSelf g) (TCTX_Bind gok htPrf) tPrf

tWeaken : (g ok) -> (g |- ht) -> (g |- e : t) -> (((_, ht) :: g) |- e : t)
tWeaken {g} gok htPrf tPrf = tThinning (IgnoreHead $ sublistSelf g) (TCTX_Bind gok htPrf) tPrf

anyTypeInCtxIsWellformed : (g ok) -> Elem (x, t) g -> (g |- t)
anyTypeInCtxIsWellformed (TCTX_Bind init twfPrf) Here = twfWeaken init twfPrf twfPrf
anyTypeInCtxIsWellformed (TCTX_Bind init twfPrf) (There later) = twfWeaken init twfPrf $ anyTypeInCtxIsWellformed init later

mutual
  {-
  substTermRBTCase : (res : SType)
                  -> (res = SRBT v2 b' Τ)
                  -> (((v, SRBT v1 b Τ) :: (x, t1) :: g) |- e' : res)
                  -> (g |- e : t1)
                  -> (((v, SRBT v1 b Τ) :: g) |- (substInTerm x e e') : SRBT v2 b' Τ)

  substPreservesCons : (g |- e : t1) -> All (\conTy => ((x, t1) :: g) |- conTy) cons -> All (\conTy => g |- conTy) (substInADT x e cons)
  substPreservesCons _ [] = []
  substPreservesCons eprf (con :: cons) = substPreservesTWF con eprf :: substPreservesCons eprf cons

  substPreservesTWF : (((x, t1) :: g) |- t2) -> (g |- e : t1) -> (g |- substInType x e t2)
  substPreservesTWF (TWF_TrueRef (TCTX_Bind gok _)) eprf = TWF_TrueRef gok
  substPreservesTWF (TWF_Base e1deriv e2deriv) eprf = TWF_Base (substTermRBTCase _ Refl e1deriv eprf) (substTermRBTCase _ Refl e2deriv eprf)
  substPreservesTWF (TWF_Conj r1deriv r2deriv) eprf = TWF_Conj (substPreservesTWF r1deriv eprf) (substPreservesTWF r2deriv eprf)
  substPreservesTWF (TWF_Arr {x} {t1} {t2} t1prf t2prf) eprf =
    let t1prf' = substPreservesTWF t1prf eprf
     in TWF_Arr t1prf' ?arg
  substPreservesTWF (TWF_ADT alls) eprf = TWF_ADT $ substPreservesCons eprf alls
             -}


substInCtx : Var -> STerm -> Ctx -> Ctx
substInCtx x e [] = []
substInCtx x e ((x', ty) :: rest) = (x', substInType x e ty) :: substInCtx x e rest

substInCtxSnoc : (x : _) -> (e : _) -> (y : _) -> (t : _) -> (g : Ctx)
              -> substInCtx x e (g ++ [(y, t)]) = substInCtx x e g ++ [(y, substInType x e t)]
substInCtxSnoc _ _ _ _ [] = Refl
substInCtxSnoc x e y t ((_, _) :: g') = cong $ substInCtxSnoc x e y t g'

tossMidElem : (front : List a) -> (mid : a) -> (back : List a)
           -> ((front ++ [mid]) ++ back) = (front ++ mid :: back)
tossMidElem [] mid back = Refl
tossMidElem (f :: front') mid back = cong $ tossMidElem front' mid back

-- g is for Γ
-- d is for Δ
subst1lemma : (g |- e : s)
           -> ((d ++ (x, s) :: g) |- tau)
           -> ((d ++ (x, s) :: g) |- substInType x e tau)

subst2lemma : (g |- e : s)
           -> ((d ++ (y, t) :: (x, s) :: g) |- tau)
           -> ((d ++ (y, substInType x e t) :: (x, s) :: g) |- tau)

subst3lemma : ((d ++ (y, t) :: (x, s) :: g) |- tau)
           -> ?t_no_x
           -> ((d ++ (x, s) :: (y, t) :: g) |- tau)

mutual
  substPreservesTWF : (g |- e : s)
                   -> ((d ++ (x, s) :: g) |- tau)
                   -> SnocList d
                   -> ((substInCtx x e d ++ g) |- substInType x e tau)
  substPreservesTWF {x} {e} {g} {d = []} eprf tauprf Empty = ?later
  substPreservesTWF {x} {e} {g} {d = d ++ [(y, t)]} eprf tauprf (Snoc init) =
    let rec = substPreservesTWF {d = d} {x = x} {g = (y, substInType x e t) :: g} (tWeaken (TWF_implies_TCTX (T_implies_TWF eprf)) ?w1 eprf) ?w2 init
     in rewrite substInCtxSnoc x e y t d
     in rewrite tossMidElem (substInCtx x e d) (y, substInType x e t) g
     in rec

  substPreservesTWFHead : (((x, t1) :: g) |- t2) -> (g |- e : t1) -> (g |- substInType x e t2)

  -- Well-formedness of a type in a context implies well-formedness of said context
  -- TODO get rid of `assert_smaller` by carrying the depth of the tree explicitly
  TWF_implies_TCTX : (g |- t) -> g ok
  TWF_implies_TCTX (TWF_TrueRef gok) = gok
  TWF_implies_TCTX (TWF_Base t1 t2) = case TWF_implies_TCTX (assert_smaller (TWF_Base t1 t2) (T_implies_TWF t1)) of
                                           TCTX_Bind gok _ => gok
  TWF_implies_TCTX (TWF_Conj twfr1 _) = TWF_implies_TCTX twfr1
  TWF_implies_TCTX (TWF_Arr twft1 _) = TWF_implies_TCTX twft1
  TWF_implies_TCTX (TWF_ADT (con1Ty :: _)) = TWF_implies_TCTX con1Ty

  -- Well-typedness of a term in a context implies well-formedness of its type in said context
  T_implies_TWF : (g |- e : t) -> (g |- t)
  T_implies_TWF (T_Unit gok) = TWF_TrueRef gok
  T_implies_TWF (T_Var gok elemPrf) = anyTypeInCtxIsWellformed gok elemPrf
  T_implies_TWF (T_Abs arrWfPrf _) = arrWfPrf
  T_implies_TWF (T_App prf1 prf2) = substPreservesTWFHead (arrWfImpliesCodWf $ T_implies_TWF prf1) prf2
  T_implies_TWF (T_Case wfPrf _ _) = wfPrf
  T_implies_TWF (T_Con _ wfPrf) = wfPrf
  T_implies_TWF (T_Sub x y) = ?T_implies_TWF_sub_hole
