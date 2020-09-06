module Surface.Derivations.Sizes

import Control.WellFounded
import Data.Nat
import Data.Vect
import Data.Vect.Quantifiers

import Surface.Derivations
import Surface.Syntax

%default total

infixl 8 .+.
public export
(.+.) : Nat -> Nat -> Nat
(.+.) = maximum

mutual
  public export
  implementation Sized (ok g) where
    size TCTX_Empty = 0
    size (TCTX_Bind prevOk tyPrf) = S (size prevOk .+. size tyPrf)

  public export
  implementation Sized (g |- t) where
    size typrf = S $ case typrf of
                          TWF_TrueRef gok => size gok
                          TWF_Base e1deriv e2deriv => size e1deriv .+. size e2deriv
                          TWF_Conj r1deriv r2deriv => size r1deriv .+. size r2deriv
                          TWF_Arr argDeriv resDeriv => size argDeriv .+. size resDeriv
                          TWF_ADT consDerivs => go consDerivs
      where
        go : All (\conTy => g |- conTy) cons -> Nat
        go [] = 0
        go (x :: xs) = size x .+. go xs

  public export
  implementation Sized (BranchesHaveType g cons bs t) where
    size bs = S $ go bs
      where
        go : BranchesHaveType g cons' bs' t -> Nat
        go NoBranches = 0
        go (OneMoreBranch eprf rest) = size eprf .+. go rest

  public export
  implementation {e : STerm} -> Sized (g |- e :. t) where
    size eprf = S $ case eprf of
                         T_Unit gok => size gok
                         T_Var gok _ => size gok
                         T_Abs arrTy bodyTy => size arrTy .+. size bodyTy
                         T_App funTy argTy => size funTy .+. size argTy
                         T_Case resTWF scrutTy bs => size resTWF .+. size scrutTy .+. size bs
                         T_Con conArg adtTy => size conArg .+. size adtTy
                         T_Sub eprf subprf => size eprf .+. size subprf

  public export
  implementation {t1 : SType} -> Sized (g |- t1 <: t2) where
    size subprf = S $ case subprf of
                           ST_Base oracle x => 0
                           ST_Arr arg res => size arg .+. size res
