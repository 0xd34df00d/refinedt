module Core.Syntax

%default total

public export
data Sort = TypeS | KindS

public export
record Var where
  constructor MkVar
  var : String

public export
data CExpr : Type where
  CVar  : (var : Var) -> CExpr
  CPi   : (var : Var) -> (e1 : CExpr) -> (e2 : CExpr) -> CExpr
  CLam  : (var : Var) -> (e1 : CExpr) -> (e2 : CExpr) -> CExpr
  CApp  : (e1 : CExpr) -> (e2 : CExpr) -> CExpr
  Cunit : CExpr
  CUnit : CExpr
