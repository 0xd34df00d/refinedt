{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards, QuasiQuotes, BlockArguments, TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Toy.Language.Solver
( solve
, SolveContext
, SolveRes(..)

, buildCtx
) where

import qualified Data.HashMap.Strict as HM
import Data.Maybe
import Data.String.Interpolate
import Control.Arrow
import Control.Monad
import Control.Monad.Reader
import Z3.Monad

import Toy.Language.BasicTC
import Toy.Language.EnvironmentUtils
import Toy.Language.Syntax.Decls
import Toy.Language.Syntax.Types

data SolveRes = Correct | Wrong deriving (Eq, Show)

newtype SolveContext = SolveContext
  { visibleSigs :: [FunSig]
  } deriving (Eq, Ord, Show, Semigroup, Monoid)

buildCtx :: [FunSig] -> SolveContext
buildCtx = SolveContext

solve :: SolveContext -> FunSig -> FunDef -> IO SolveRes
solve ctx sig def = evalZ3 $ mkScript ctx arg2type resType (funBody def)
  where
    (argTypes, resType) = splitTypes sig
    arg2type = zip (funArgs def) argTypes

newtype Z3VarName = Z3VarName { getZ3VarName :: AST }

newtype SolveEnvironment = SolveEnvironment
  { z3args :: HM.HashMap VarName (Ty, Z3VarName)
  }

-- This expects that the pi-binders names in the type are equal to the argument names in the definition.
-- TODO explicitly check for this.
mkScript :: SolveContext -> ArgTypes -> RefinedBaseTy -> Term -> Z3 SolveRes
mkScript ctx args target term = do
  solveEnv <- buildSolveEnv (visibleSigs ctx) args

  convertZ3Result <$> flip runReaderT solveEnv do
    argsPresup <- genArgsPresup

    res <- Z3VarName <$> mkFreshTypedVar (baseType target) "_res$"
    resConcl <- genRefinementCstrs target res >>= mkAnd

    typedTerm <- annotateTypes term

    TermsCstrs { .. } <- genTermsCstrs res typedTerm
    case mandatoryCstrs of
         Just cstrs -> assert cstrs
         Nothing -> pure ()
    refutables <- maybe mkTrue pure refutableCstrs
    termCstrsConsistent <- solverCheckAssumptions [refutables]
    case termCstrsConsistent of
         Sat -> do
            assert refutables
            assert =<< mkNot =<< argsPresup `mkImplies` resConcl
            invert <$> check
         c -> pure c

    {-
    res <- check
    getModel >>= modelToString . fromJust . snd >>= liftIO . putStrLn
    pure $ invert res
    -}
  where
    invert Sat = Unsat
    invert Unsat = Sat
    invert Undef = Undef

buildSolveEnv :: MonadZ3 m => [FunSig] -> ArgTypes -> m SolveEnvironment
buildSolveEnv sigs args = fmap SolveEnvironment $ buildCombinedMapping sigs args $ \name ty -> (ty,) . Z3VarName <$> mkZ3Var (getName name) ty
  where
    mkZ3Var varName (TyBase rbty) = mkFreshTypedVar (baseType rbty) varName
    mkZ3Var varName _ = mkStringSymbol varName >>= mkUninterpretedSort >>= mkFreshConst varName -- TODO fun decl?

mkFreshTypedVar :: MonadZ3 m => BaseTy -> String -> m AST
mkFreshTypedVar TInt = mkFreshIntVar
mkFreshTypedVar TBool = mkFreshBoolVar
mkFreshTypedVar TIntList = error "TODO TIntList unsupported" -- TODO

buildCtxVars :: [FunSig] -> Z3 (HM.HashMap VarName (Ty, Z3VarName))
buildCtxVars sigs = buildZ3Vars [ (VarName funName, funTy) | FunSig { .. } <- sigs ]

data TermsCstrs = TermsCstrs
  { mandatoryCstrs :: Maybe AST
  , refutableCstrs :: Maybe AST
  }

mandatory :: AST -> TermsCstrs
mandatory cstr = TermsCstrs (Just cstr) Nothing

refutable :: AST -> TermsCstrs
refutable cstr = TermsCstrs Nothing (Just cstr)

andTermsCstrs :: MonadZ3 m => [TermsCstrs] -> m TermsCstrs
andTermsCstrs cstrs = TermsCstrs <$> mkAnd' mandatories <*> mkAnd' refutables
  where
    mandatories = mapMaybe mandatoryCstrs cstrs
    refutables = mapMaybe refutableCstrs cstrs
    mkAnd' [] = pure Nothing
    mkAnd' [c] = pure $ Just c
    mkAnd' cs = Just <$> mkAnd cs

implyTermsCstrs :: MonadZ3 m => AST -> TermsCstrs -> m TermsCstrs
implyTermsCstrs presupp TermsCstrs { .. } = do
  mandatory' <- mkImplies' mandatoryCstrs
  refutable' <- mkImplies' refutableCstrs
  pure $ TermsCstrs mandatory' refutable'
  where
    mkImplies' = traverse $ mkImplies presupp

genTermsCstrs :: (MonadZ3 m, MonadReader SolveEnvironment m) => Z3VarName -> TypedTerm -> m TermsCstrs
genTermsCstrs termVar (TName _ varName) = do
  z3Var <- askZ3VarName varName
  mandatory <$> getZ3VarName termVar `mkEq` z3Var
genTermsCstrs termVar (TInteger _ n) = do
  num <- mkIntNum n
  mandatory <$> getZ3VarName termVar `mkEq` num
genTermsCstrs termVar (TBinOp _ t1 op t2) = do
  (t1var, t1cstrs) <- mkVarCstrs "_linkVar_t1$" t1
  (t2var, t2cstrs) <- mkVarCstrs "_linkVar_t2$" t2
  bodyRes <- z3op t1var t2var
  bodyCstr <- mandatory <$> getZ3VarName termVar `mkEq` bodyRes
  andTermsCstrs [t1cstrs, t2cstrs, bodyCstr]
  where
    z3op = case op of
                BinOpPlus -> \a b -> mkAdd [a, b]
                BinOpMinus -> \a b -> mkSub [a, b]
                BinOpGt -> mkGt
                BinOpLt -> mkLt
genTermsCstrs termVar TIfThenElse { .. } = do
  condVar <- mkFreshBoolVar "_condVar$"
  condCstrs <- genTermsCstrs (Z3VarName condVar) tcond

  (thenVar, thenCstrs) <- mkVarCstrs "_linkVar_tthen$" tthen
  (elseVar, elseCstrs) <- mkVarCstrs "_linkVar_telse$" telse

  thenClause <- do
    thenEq <- mandatory <$> getZ3VarName termVar `mkEq` thenVar
    entails <- andTermsCstrs [thenCstrs, thenEq]
    implyTermsCstrs condVar entails
  elseClause <- do
    elseEq <- mandatory <$> getZ3VarName termVar `mkEq` elseVar
    notCondVar <- mkNot condVar
    entails <- andTermsCstrs [elseCstrs, elseEq]
    implyTermsCstrs notCondVar entails

  andTermsCstrs [condCstrs, thenClause, elseClause]
genTermsCstrs termVar (TApp resTy fun arg) = do
  subTyCstr <- case (annotation fun, annotation arg) of
                    (TyArrow ArrowTy { domTy = expectedTy }, actualTy) -> expectedTy <: actualTy
                    (_, _) -> error "Function should have arrow type (this should've been caught earlier though)"

  resCstr <- case resTy of
                  TyArrow _ -> pure Nothing
                  TyBase rbt -> fmap Just $ genRefinementCstrs rbt termVar >>= mkAnd

  andTermsCstrs [TermsCstrs Nothing resCstr, TermsCstrs Nothing $ Just subTyCstr]

-- generate constraints for the combination of the function type and its argument type:
-- the refinements of the first Ty should be a subtype (that is, imply) the refinements of the second Ty
(<:) :: (MonadZ3 m, MonadReader SolveEnvironment m) => Ty -> Ty -> m AST
TyBase rbtExpected <: TyBase rbtActual = do
  -- the refinements language only supports refinements over integers, so it's ok to assume the type is int here
  v <- Z3VarName <$> mkFreshIntVar "_∀_v$"

  actualCstr <- genRefinementCstrs rbtActual v >>= mkAnd
  expectedCstr <- genRefinementCstrs rbtExpected v >>= mkAnd
  implication <- mkImplies actualCstr expectedCstr

  v' <- toApp $ getZ3VarName v
  mkForallConst [] [v'] implication
TyArrow (ArrowTy _ funDomTy funCodTy) <: TyArrow (ArrowTy _ argDomTy argCodTy) = do
  argCstrs <- argDomTy <: funDomTy
  funCstrs <- funCodTy <: argCodTy
  mkAnd [argCstrs, funCstrs]
ty1 <: ty2 = error [i|Mismatched types #{ty1} #{ty2} (which should've been caught earlier though)|]

mkVarCstrs :: (MonadZ3 m, MonadReader SolveEnvironment m) => String -> TypedTerm -> m (AST, TermsCstrs)
mkVarCstrs name term = do
  var <- mkFreshTypedVar ((\(TyBase rbty) -> baseType rbty) $ annotation term) name
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
                    RArgInt n -> mkIntNum n
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

askVarTy :: MonadReader SolveEnvironment m => VarName -> m Ty
askVarTy var = asks (fst . (HM.! var) . z3args)

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
