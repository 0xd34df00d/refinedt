{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}

module Toy.Language.Solver where

import qualified Data.HashMap.Strict as HM
import Control.Arrow
import Control.Monad
import Z3.Monad

import Toy.Language.Syntax.Decls
import Toy.Language.Syntax.Types

data SolveRes = Satisfied | Unsatisfied deriving (Eq, Show)

newtype SolveContext = SolveContext
  { visibleSigs :: HM.HashMap String FunSig
  } deriving (Eq, Ord, Show, Semigroup, Monoid)

solve :: SolveContext -> FunSig -> FunDef -> IO SolveRes
solve _ sig def = evalZ3 $ mkScript arg2type resType (funBody def)
  where
    (argTypes, resType) = splitTypes sig
    arg2type = HM.fromList $ zip (funArgs def) argTypes

type ArgTypes = HM.HashMap VarName Ty

newtype Z3VarName = Z3VarName { getZ3VarName :: AST }

-- This expects that the pi-binders names in the type are equal to the argument names in the definition.
-- TODO explicitly check for this.
mkScript :: ArgTypes -> RefinedBaseTy -> Term -> Z3 SolveRes
mkScript args target term = do
  z3vars <- HM.fromList <$> mapM sequence [ (var, Z3VarName <$> mkFreshIntVar (getName var))
                                          | (var, TyBase RefinedBaseTy { baseType = TInt }) <- HM.toList args
                                          ]
  let z3args = HM.intersectionWith (,) args z3vars

  argsPresup <- genArgsPresup z3args

  res <- Z3VarName <$> mkFreshIntVar "_res$" -- TODO don't assume result : Int
  resConcl <- genRefinementCstrs z3args target res >>= mkAnd

  assert =<< argsPresup `mkImplies` resConcl

  convertZ3Result <$> check

type ArgZ3Types = HM.HashMap VarName (Ty, Z3VarName)

genArgsPresup :: ArgZ3Types -> Z3 AST
genArgsPresup z3args = foldM addVar [] (HM.elems z3args) >>= mkAnd
  where
    addVar cstrs (TyBase rbTy, z3var) = (cstrs <>) <$> genRefinementCstrs z3args rbTy z3var
    addVar cstrs _ = pure cstrs

genRefinementCstrs :: ArgZ3Types -> RefinedBaseTy -> Z3VarName -> Z3 [AST]
genRefinementCstrs z3args rbTy z3var
  | not $ null conjs = do
    when (baseType rbTy /= TInt) $ error "Non-int refinements unsupported for now"
    mapM (genCstr $ getZ3VarName z3var) conjs
  | otherwise = pure []
  where
    conjs = conjuncts $ baseTyRefinement rbTy

    genCstr v (AR op arg) = do
      z3arg <- case arg of
                    RArgZero -> mkInteger 0
                    RArgVar var -> pure $ getZ3VarName $ snd $ z3args HM.! var
                    RArgVarLen _ -> error "TODO" -- TODO
      v `z3op` z3arg
      where
        z3op = case op of
                    ROpLt -> mkLt
                    ROpLeq -> mkLe
                    ROpEq -> mkEq
                    ROpNEq -> \a b -> mkNot =<< mkEq a b
                    ROpGt -> mkGt
                    ROpGeq -> mkGe

convertZ3Result :: Result -> SolveRes
convertZ3Result Sat = Satisfied
convertZ3Result Unsat = Unsatisfied
convertZ3Result Undef = Unsatisfied -- TODO

splitTypes :: FunSig -> ([Ty], RefinedBaseTy)
splitTypes = go . funTy
  where
    go (TyBase rbTy) = ([], rbTy)
    go (TyArrow ArrowTy { .. }) = first (domTy :) $ go codTy
