module Surface.Theorems

import Data.Fin
import Data.List
import Data.Vect
import Data.Vect.Quantifiers

import Surface.Syntax
import Surface.Derivations

%default total

-- Well-typedness of a term in a context implies well-formedness of said context
T_implies_TCTX : (g |- e : t) -> g ok
T_implies_TCTX (T_Unit gok) = gok
T_implies_TCTX (T_Var gok _) = gok
T_implies_TCTX (T_Abs subDer) = case T_implies_TCTX subDer of
                                     TCTX_Bind init _ => init
T_implies_TCTX (T_App subDer _) = T_implies_TCTX subDer
T_implies_TCTX (T_Case _ subDer _) = T_implies_TCTX subDer
T_implies_TCTX (T_Con subDer _) = T_implies_TCTX subDer
T_implies_TCTX (T_Sub subDer _) = T_implies_TCTX subDer


-- Well-typedness of a term in a context implies well-formedness of its type in said context

data Sublist : (sub : List a) -> (ls : List a) -> Type where
  EmptyIsSublist  : Sublist [] ls
  IgnoreHead      : Sublist sub ls -> Sublist sub (_ :: ls)
  AppendBoth      : Sublist sub ls -> Sublist (x :: sub) (x :: ls)

sublistSelf : (ls : List a) -> Sublist ls ls
sublistSelf [] = EmptyIsSublist
sublistSelf (_ :: xs) = AppendBoth $ sublistSelf xs

mutual
  twfThinning : Sublist g g' -> (g |- t) -> (g' |- t)
  twfThinning _ TWF_TrueRef = TWF_TrueRef
  twfThinning subPrf (TWF_Base t1 t2) = TWF_Base (tThinning (AppendBoth subPrf) t1) (tThinning (AppendBoth subPrf) t2)
  twfThinning subPrf (TWF_Conj twfr1 twfr2) = TWF_Conj (twfThinning subPrf twfr1) (twfThinning subPrf twfr2)
  twfThinning subPrf (TWF_Arr twf1 twf2) = TWF_Arr (twfThinning subPrf twf1) (twfThinning (AppendBoth subPrf) twf2)
  twfThinning subPrf (TWF_ADT preds) = TWF_ADT (thinAll subPrf preds)
    where
      thinAll : Sublist g g' -> All (\t => g |- t) ls -> All (\t => g' |- t) ls
      thinAll _ [] = []
      thinAll subPrf (a :: as) = twfThinning subPrf a :: thinAll subPrf as

  twfWeaken : (g |- t) -> ((_ :: g) |- t)
  twfWeaken {g} = twfThinning (IgnoreHead $ sublistSelf g)

  anyTypeInCtxIsWellformed : (g ok) -> Elem (x, t) g -> (g |- t)
  anyTypeInCtxIsWellformed (TCTX_Bind _ twfPrf) Here = twfWeaken twfPrf
  anyTypeInCtxIsWellformed (TCTX_Bind init _) (There later) = twfWeaken $ anyTypeInCtxIsWellformed init later

  tThinning : Sublist g g' -> (g |- e : t) -> (g' |- e : t)

  T_implies_TWF : (g |- e : t) -> (g |- t)
  T_implies_TWF (T_Unit _) = TWF_TrueRef
  T_implies_TWF (T_Var gok elemPrf) = anyTypeInCtxIsWellformed gok elemPrf
  T_implies_TWF (T_Abs y) = ?T_implies_TWF_rhs_3
  T_implies_TWF (T_App y z) = ?T_implies_TWF_rhs_4
  T_implies_TWF (T_Case x y z) = ?T_implies_TWF_rhs_5
  T_implies_TWF (T_Con x y) = ?T_implies_TWF_rhs_6
  T_implies_TWF (T_Sub x y) = ?T_implies_TWF_rhs_7
