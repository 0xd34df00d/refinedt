module Surface.Theorems.TCTX

import Data.List.Elem
import Data.Vect
import Data.Vect.Quantifiers

import Surface.Syntax
import Surface.Derivations

%default total

-- Well-typedness of a term in a context implies well-formedness of said context
export
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
export
TWF_implies_TCTX : (g |- t) -> ok g
TWF_implies_TCTX (TWF_TrueRef gok) = gok
TWF_implies_TCTX (TWF_Base t1 _) = case T_implies_TCTX t1 of
                                         TCTX_Bind gok _ => gok
TWF_implies_TCTX (TWF_Conj twfr1 _) = TWF_implies_TCTX twfr1
TWF_implies_TCTX (TWF_Arr twft1 _) = TWF_implies_TCTX twft1
TWF_implies_TCTX (TWF_ADT (con1Ty :: _)) = TWF_implies_TCTX con1Ty
