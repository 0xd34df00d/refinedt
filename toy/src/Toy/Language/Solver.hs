{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}

module Toy.Language.Solver where

import qualified Data.HashMap.Strict as HM
import Control.Arrow
import Control.Monad
import Data.Functor
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

-- This expects that the pi-binders names in the type are equal to the argument names in the definition.
-- TODO explicitly check for this.
mkScript :: ArgTypes -> Ty -> Term -> Z3 SolveRes
mkScript args target term = do
  z3vars <- HM.fromList <$> mapM sequence [ (var, mkFreshIntVar $ getName var)
                                          | (var, TyBase RefinedBaseTy { baseType = TInt }) <- HM.toList args
                                          ]
  assertArgsCstrs $ HM.intersectionWith (,) args z3vars
  pure undefined

assertArgsCstrs :: HM.HashMap VarName (Ty, AST) -> Z3 ()
assertArgsCstrs args = allCstrs $> ()
  where
    allCstrs = foldM addVar [] $ HM.elems args

    addVar cstrs (TyBase rbt, z3var) | not $ null conjs = do
      when (baseType rbt /= TInt) $ error "Non-int refinements unsupported for now"
      varCstrs <- mapM (genCstr z3var) conjs
      pure $ cstrs <> varCstrs
      where
        conjs = conjuncts $ baseTyRefinement rbt
    addVar cstrs _ = pure cstrs

    genCstr v (AR op arg) = do
      z3arg <- case arg of
                    RArgZero -> mkInteger 0
                    RArgVar var -> pure $ snd $ args HM.! var
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

splitTypes :: FunSig -> ([Ty], Ty)
splitTypes = go . funTy
  where
    go ty@TyBase {} = ([], ty)
    go (TyArrow ArrowTy { .. }) = first (domTy :) $ go codTy
