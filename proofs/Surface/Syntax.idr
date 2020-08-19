module Surface.Syntax

%default total
%access public export

record ADTLabel where
  constructor MkADTLabel
  label : String

record Var where
  constructor MkVar
  var : String

mutual
  data STerm : Type where
    SVar  : (var : Var) -> STerm
    SLam  : (var : Var) -> (t : SType) -> (e : STerm) -> STerm
    SApp  : (e1 : STerm) -> (e2 : STerm) -> STerm
    SUnit : STerm
    SCase : (scrut : STerm) -> (branches : List CaseBranch) -> STerm
    SCon  : (label : ADTLabel) -> (body : STerm) -> (adtCons : ADTCons) -> STerm

  record CaseBranch where
    constructor MkCaseBranch
    label : ADTLabel
    var : Var
    body : STerm

  data BaseType = BUnit

  infixl 6 &
  infixl 7 |=|
  data Refinement = (|=|) STerm STerm
                  | (&) Refinement Refinement
  %name Refinement r, r1, r2

  ADTCons : Type
  ADTCons = List (ADTLabel, SType)

  data SType : Type where
    SRBT : (var : Var) -> (b : BaseType) -> (ref : Refinement) -> SType
    SArr : (var : Var) -> (t1 : SType) -> (t2 : SType) -> SType
    SADT : (cons : ADTCons) -> SType

isValue : STerm -> Bool
isValue (SVar _) = True
isValue SUnit = True
isValue (SCon _ body _) = isValue body
isValue _ = False

data Ctx = MkCtx (List (Var, SType))

-- Helpers

Empty : Ctx
Empty = MkCtx []

(::) : (Var, SType) -> Ctx -> Ctx
(::) p (MkCtx lst) = MkCtx $ p :: lst

Τ : Refinement
Τ = SUnit |=| SUnit

syntax "{" [v] ":" [b] "|" [r] "}" = SRBT v b r
