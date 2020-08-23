module Surface.Theorems

import Data.Fin
import Data.List
import Data.Vect
import Data.Vect.Quantifiers

import Surface.Syntax
import Surface.Derivations

%default total

data Sublist : (sub : List a) -> (ls : List a) -> Type where
  EmptyIsSublist  : Sublist [] ls
  IgnoreHead      : Sublist sub ls -> Sublist sub (_ :: ls)
  AppendBoth      : Sublist sub ls -> Sublist (x :: sub) (x :: ls)

sublistSelf : (ls : List a) -> Sublist ls ls
sublistSelf [] = EmptyIsSublist
sublistSelf (_ :: xs) = AppendBoth $ sublistSelf xs

mutual
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

  twfThinning : Sublist g g' -> g' ok -> (g |- t) -> (g' |- t)
  twfThinning _      g'ok (TWF_TrueRef g') = TWF_TrueRef g'ok
  twfThinning subPrf g'ok (TWF_Base t1 t2) = TWF_Base (tThinning (AppendBoth subPrf) t1) (tThinning (AppendBoth subPrf) t2)
  twfThinning subPrf g'ok (TWF_Conj twfr1 twfr2) = TWF_Conj (twfThinning subPrf g'ok twfr1) (twfThinning subPrf g'ok twfr2)
  twfThinning subPrf g'ok (TWF_Arr twf1 twf2) = TWF_Arr
                                                  (twfThinning subPrf g'ok twf1)
                                                  (twfThinning (AppendBoth subPrf) (TCTX_Bind g'ok (twfThinning subPrf g'ok twf1)) twf2)
  twfThinning subPrf g'ok (TWF_ADT preds) = TWF_ADT (thinAll subPrf g'ok preds)
    where
      thinAll : Sublist g g' -> g' ok -> All (\t => g |- t) ls -> All (\t => g' |- t) ls
      thinAll _ _ [] = []
      thinAll subPrf g'ok (a :: as) = twfThinning subPrf g'ok a :: thinAll subPrf g'ok as

  twfWeaken : (g |- ht) -> (g |- t) -> (((_, ht) :: g) |- t)
  twfWeaken {g} hPrf ctxPrf = let g'ok = TCTX_Bind (TWF_implies_TCTX ctxPrf) hPrf
                               in twfThinning (IgnoreHead $ sublistSelf g) g'ok ctxPrf

  anyTypeInCtxIsWellformed : (g ok) -> Elem (x, t) g -> (g |- t)
  anyTypeInCtxIsWellformed (TCTX_Bind _ twfPrf) Here = twfWeaken twfPrf twfPrf
  anyTypeInCtxIsWellformed (TCTX_Bind init twfPrf) (There later) = twfWeaken twfPrf $ anyTypeInCtxIsWellformed init later

  tThinning : Sublist g g' -> (g |- e : t) -> (g' |- e : t)

  T_implies_TWF : (g |- e : t) -> (g |- t)
  T_implies_TWF (T_Unit _) = TWF_TrueRef
  T_implies_TWF (T_Var gok elemPrf) = anyTypeInCtxIsWellformed gok elemPrf
  T_implies_TWF (T_Abs y) = ?T_implies_TWF_rhs_3
  T_implies_TWF (T_App y z) = ?T_implies_TWF_rhs_4
  T_implies_TWF (T_Case x y z) = ?T_implies_TWF_rhs_5
  T_implies_TWF (T_Con x y) = ?T_implies_TWF_rhs_6
  T_implies_TWF (T_Sub x y) = ?T_implies_TWF_rhs_7
