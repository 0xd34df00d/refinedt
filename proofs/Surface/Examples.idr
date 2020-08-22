module Surface.Examples

import Data.List

import Surface.Derivations
import Surface.Syntax

VarX : Var
VarX = MkVar "x"

VarV : Var
VarV = MkVar "v"

SomeType : SType
SomeType = { VarV : BUnit | Τ }

T_nontrivial1 : ([] |- (SLam VarX SomeType (SVar VarX)) : SArr VarX SomeType SomeType)
T_nontrivial1 = T_Abs (T_Var (TCTX_Bind TCTX_Empty TWF_TrueRef) Here)
