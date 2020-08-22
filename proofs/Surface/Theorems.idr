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
