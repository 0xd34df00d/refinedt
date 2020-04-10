{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}

module Toy.Language.Solver where

import qualified Data.HashMap.Strict as HM
import Control.Arrow
import Control.Monad
import Control.Monad.Reader
import Z3.Monad

import Toy.Language.Syntax.Decls
import Toy.Language.Syntax.Types

data SolveRes = Correct | Wrong deriving (Eq, Show)

newtype SolveContext = SolveContext
  { visibleSigs :: HM.HashMap String FunSig
  } deriving (Eq, Ord, Show, Semigroup, Monoid)

solve :: SolveContext -> FunSig -> FunDef -> IO SolveRes
solve ctx sig def = evalZ3 $ mkScript ctx arg2type resType (funBody def)
  where
    (argTypes, resType) = splitTypes sig
    arg2type = HM.fromList $ zip (funArgs def) argTypes

type ArgTypes = HM.HashMap VarName Ty

newtype Z3VarName = Z3VarName { getZ3VarName :: AST }

data SolveEnvironment = SolveEnvironment
  { ctx :: SolveContext
  , z3args :: ArgZ3Types
  }

-- This expects that the pi-binders names in the type are equal to the argument names in the definition.
-- TODO explicitly check for this.
mkScript :: SolveContext -> ArgTypes -> RefinedBaseTy -> Term -> Z3 SolveRes
mkScript ctx args target term = do
  z3vars <- HM.fromList <$> mapM sequence [ (var, Z3VarName <$> mkFreshIntVar (getName var))
                                          | (var, TyBase RefinedBaseTy { baseType = TInt }) <- HM.toList args
                                          ]
  let z3args = HM.intersectionWith (,) args z3vars
  let solveEnv = SolveEnvironment { .. }

  flip runReaderT solveEnv $ do
    argsPresup <- genArgsPresup

    res <- Z3VarName <$> mkFreshIntVar "_res$" -- TODO don't assume result : Int
    resConcl <- genRefinementCstrs target res >>= mkAnd

    assert =<< genTermsCstrs res term

    assert =<< mkNot =<< argsPresup `mkImplies` resConcl

  --getModel >>= modelToString . fromJust . snd >>= liftIO . putStrLn

  convertZ3Result . invert <$> check
  where
    invert Sat = Unsat
    invert Unsat = Sat
    invert Undef = Undef

type ArgZ3Types = HM.HashMap VarName (Ty, Z3VarName)

genTermsCstrs :: (MonadZ3 m, MonadReader SolveEnvironment m) => Z3VarName -> Term -> m AST
genTermsCstrs termVar (TBinOp t1 op t2) = do
  -- these are necessarily ints since binops are always working with ints
  (t1var, t1cstrs) <- mkIntVarCstrs "_linkVar_t1$" t1
  (t2var, t2cstrs) <- mkIntVarCstrs "_linkVar_t2$" t2
  bodyRes <- z3op t1var t2var
  bodyCstr <- getZ3VarName termVar `mkEq` bodyRes
  mkAnd [t1cstrs, t2cstrs, bodyCstr]
  where
    z3op = case op of
                BinOpPlus -> \a b -> mkAdd [a, b]
                BinOpMinus -> \a b -> mkSub [a, b]
                BinOpGt -> mkGt
                BinOpLt -> mkLt
genTermsCstrs termVar (TName varName) = do
  z3Var <- askZ3VarName varName
  getZ3VarName termVar `mkEq` z3Var

mkIntVarCstrs :: (MonadZ3 m, MonadReader SolveEnvironment m) => String -> Term -> m (AST, AST)
mkIntVarCstrs name term = do
  var <- mkFreshIntVar name
  cstrs <- genTermsCstrs (Z3VarName var) term
  pure (var, cstrs)

genArgsPresup :: (MonadZ3 m, MonadReader SolveEnvironment m) => m AST
genArgsPresup = do
  args <- asks $ HM.elems . z3args
  foldM addVar [] args >>= mkAnd
  where
    addVar cstrs (TyBase rbTy, z3var) = (cstrs <>) <$> genRefinementCstrs rbTy z3var
    addVar cstrs _ = pure cstrs

genRefinementCstrs :: (MonadZ3 m, MonadReader SolveEnvironment m) => RefinedBaseTy -> Z3VarName -> m [AST]
genRefinementCstrs rbTy z3var
  | not $ null conjs = do
    when (baseType rbTy /= TInt) $ error "Non-int refinements unsupported for now"
    mapM (genCstr $ getZ3VarName z3var) conjs
  | otherwise = pure []
  where
    conjs = conjuncts $ baseTyRefinement rbTy

    genCstr v (AR op arg) = do
      z3arg <- case arg of
                    RArgZero -> mkInteger 0
                    RArgVar var -> askZ3VarName var
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

askZ3VarName :: MonadReader SolveEnvironment m => VarName -> m AST
askZ3VarName var = getZ3VarName <$> asks (snd . (HM.! var) . z3args)

convertZ3Result :: Result -> SolveRes
convertZ3Result Sat = Correct
convertZ3Result Unsat = Wrong
convertZ3Result Undef = Wrong -- TODO

splitTypes :: FunSig -> ([Ty], RefinedBaseTy)
splitTypes = go . funTy
  where
    go (TyBase rbTy) = ([], rbTy)
    go (TyArrow ArrowTy { .. }) = first (domTy :) $ go codTy

instance MonadZ3 m => MonadZ3 (ReaderT r m) where
  getSolver = ReaderT $ const getSolver
  getContext = ReaderT $ const getContext
