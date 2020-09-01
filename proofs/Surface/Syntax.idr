module Surface.Syntax

import Data.Vect
import Decidable.Equality

%default total

public export
record Var where
  constructor MkVar
  var : String

public export
Eq Var where
  (==) v1 v2 = var v1 == var v2
  (/=) v1 v2 = var v1 /= var v2

public export
DecEq Var where
  decEq (MkVar var1) (MkVar var2) = case decEq var1 var2 of
                                         Yes Refl => Yes Refl
                                         No contra => No $ \(Refl) => contra Refl

public export
data BaseType = BUnit

mutual
  public export
  data STerm : Type where
    SVar  : (var : Var) -> STerm
    SLam  : (var : Var) -> (t : SType) -> (e : STerm) -> STerm
    SApp  : (e1 : STerm) -> (e2 : STerm) -> STerm
    SUnit : STerm
    SCase : (scrut : STerm) -> (branches : CaseBranches n) -> STerm
    SCon  : (idx : Fin n) -> (body : STerm) -> (adtCons : ADTCons n) -> STerm

  public export
  data SType : Type where
    SRBT : (var : Var) -> (b : BaseType) -> (ref : Refinement) -> SType
    SArr : (var : Var) -> (t1 : SType) -> (t2 : SType) -> SType
    SADT : (cons : ADTCons (S n)) -> SType

  public export
  record CaseBranch where
    constructor MkCaseBranch
    var : Var
    body : STerm

  infixl 6 /\
  infixl 7 |=|
  public export
  data Refinement = (|=|) STerm STerm
                  | (/\) Refinement Refinement
  %name Refinement r, r1, r2

  public export
  ADTCons : Nat -> Type
  ADTCons n = Vect n SType

  public export
  CaseBranches : Nat -> Type
  CaseBranches n = Vect n CaseBranch

public export
isValue : STerm -> Bool
isValue (SVar _) = True
isValue SUnit = True
isValue (SCon _ body _) = isValue body
isValue _ = False

public export
CtxElem : Type
CtxElem = (Var, SType)

public export
Ctx : Type
Ctx = List CtxElem

-- Helpers

public export
Τ : Refinement
Τ = SUnit |=| SUnit

mutual
  public export
  substInType : Var -> STerm -> SType -> SType
  substInType x e (SRBT var b ref) = SRBT var b $ substInRef x e ref
  substInType x e (SArr var t1 t2) = SArr var (substInType x e t1) (substInType x e t2)
  substInType x e (SADT cons) = SADT $ substInADT x e cons

  public export
  substInRef : Var -> STerm -> Refinement -> Refinement
  substInRef x e (e1 |=| e2) = substInTerm x e e1 |=| substInTerm x e e2
  substInRef x e (r1 /\ r2) = substInRef x e r1 /\ substInRef x e r2

  public export
  substInTerm : Var -> STerm -> STerm -> STerm
  substInTerm x e (SVar var) = case decEq x var of
                                    Yes _ => e
                                    No _ => SVar var
  substInTerm x e (SLam var t body) = SLam var t $ case decEq x var of
                                                        Yes _ => body
                                                        No _ => substInTerm x e body
  substInTerm x e (SApp e1 e2) = SApp (substInTerm x e e1) (substInTerm x e e2)
  substInTerm x e SUnit = SUnit
  substInTerm x e (SCase scrut branches) = SCase (substInTerm x e scrut) (substInBranches x e branches)
  substInTerm x e (SCon idx body adtCons) = SCon idx (substInTerm x e body) (substInADT x e adtCons)

  public export
  substInADT : Var -> STerm -> ADTCons n -> ADTCons n
  substInADT x e [] = []
  substInADT x e (ty :: xs) = substInType x e ty :: substInADT x e xs
  -- TODO can we have `map` here while keeping the totality checker happy?

  public export
  substInBranches : Var -> STerm -> CaseBranches n -> CaseBranches n
  substInBranches x e [] = []
  substInBranches x e (b@(MkCaseBranch var body) :: bs) =
    let this = case decEq x var of
                    Yes _ => b
                    No _ => MkCaseBranch var $ substInTerm x e body
        rest = substInBranches x e bs
    in this :: rest

public export
substInCtx : Var -> STerm -> Ctx -> Ctx
substInCtx x e [] = []
substInCtx x e ((x', ty) :: rest) = (x', substInType x e ty) :: substInCtx x e rest

export
substInCtxSnoc : (x, e, y, t, g : _)
              -> substInCtx x e (g ++ [(y, t)]) = substInCtx x e g ++ [(y, substInType x e t)]
substInCtxSnoc _ _ _ _ [] = Refl
substInCtxSnoc x e y t ((_, _) :: g') = rewrite substInCtxSnoc x e y t g' in Refl
