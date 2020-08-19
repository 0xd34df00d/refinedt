module Surface

%default total

-- Syntax

record ADTLabel where
  constructor MkADTLabel
  label : String

record Var where
  constructor MkVar
  var : String

mutual
  data STerm : Type where
    SVar  : (var : Var) -> STerm
    SLam  : (var : Var) -> (varTy : SType) -> (body : STerm) -> STerm
    SApp  : (e1 : STerm) -> (e2 : STerm) -> STerm
    SUnit : STerm
    SCase : (scrut : STerm) -> (branches : List CaseBranch) -> STerm
    SCon  : (label : ADTLabel) -> (body : STerm) -> (adtTy : ADTDef) -> STerm

  record CaseBranch where
    constructor MkCaseBranch
    label : ADTLabel
    var : Var
    body : STerm

  data BaseType = BUnit

  data Refinement = MkRefinement (List (STerm, STerm))

  ADTDef : Type
  ADTDef = List (ADTLabel, SType)

  data SType : Type where
    SRBT : BaseType -> Refinement -> SType
    SArr : (var : Var) -> (t1 : SType) -> (t2 : SType) -> SType
    SADT : ADTDef -> SType

isValue : STerm -> Bool
isValue (SVar _) = True
isValue SUnit = True
isValue (SCon _ body _) = isValue body
isValue _ = False

data Context = MkContext (List (Var, SType))
