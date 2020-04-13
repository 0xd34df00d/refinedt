{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards, QuasiQuotes, BlockArguments #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Toy.Language.Solver
( solve
, SolveContext
, SolveRes(..)

, buildCtx
) where

import qualified Data.HashMap.Strict as HM
import Data.Generics.Uniplate.Data
import Data.String.Interpolate
import Control.Arrow
import Control.Monad
import Control.Monad.Reader
import Z3.Monad

import Toy.Language.Syntax.Decls
import Toy.Language.Syntax.Types

data SolveRes = Correct | Wrong deriving (Eq, Show)

newtype SolveContext = SolveContext
  { visibleSigs :: [FunSig]
  } deriving (Eq, Ord, Show, Semigroup, Monoid)

buildCtx :: [FunSig] -> SolveContext
buildCtx = SolveContext -- SolveContext $ HM.fromList [ (funName, sig) | sig@FunSig { .. } <- sigs ]

solve :: SolveContext -> FunSig -> FunDef -> IO SolveRes
solve ctx sig def = evalZ3 $ mkScript ctx arg2type resType (funBody def)
  where
    (argTypes, resType) = splitTypes sig
    arg2type = HM.fromList $ zip (funArgs def) argTypes

type ArgTypes = HM.HashMap VarName Ty

newtype Z3VarName = Z3VarName { getZ3VarName :: AST }

newtype SolveEnvironment = SolveEnvironment
  { z3args :: HM.HashMap VarName (Ty, Z3VarName)
  }

-- This expects that the pi-binders names in the type are equal to the argument names in the definition.
-- TODO explicitly check for this.
mkScript :: SolveContext -> ArgTypes -> RefinedBaseTy -> Term -> Z3 SolveRes
mkScript ctx args target term = do
  argVars <- buildZ3Vars args
  ctxVars <- buildCtxVars $ visibleSigs ctx
  let solveEnv = SolveEnvironment $ argVars <> ctxVars

  convertZ3Result <$> flip runReaderT solveEnv do
    argsPresup <- genArgsPresup

    res <- Z3VarName <$> mkFreshIntVar "_res$" -- TODO don't assume result : Int
    resConcl <- genRefinementCstrs target res >>= mkAnd

    typedTerm <- annotateTypes term

    termCstrs <- genTermsCstrs res typedTerm

    termCstrsConsistent <- solverCheckAssumptions [termCstrs]
    case termCstrsConsistent of
         Sat -> do
            assert termCstrs
            assert =<< mkNot =<< argsPresup `mkImplies` resConcl
            invert <$> check
         c -> pure c

  {-
  res <- check
  getModel >>= modelToString . fromJust . snd >>= liftIO . putStrLn
  pure $ convertZ3Result $ invert res
  -}
  where
    invert Sat = Unsat
    invert Unsat = Sat
    invert Undef = Undef

buildZ3Vars :: ArgTypes -> Z3 (HM.HashMap VarName (Ty, Z3VarName))
buildZ3Vars args = do
  z3vars <- HM.fromList <$> mapM sequence [ (var, Z3VarName <$> mkFreshIntVar (getName var))
                                          | (var, TyBase RefinedBaseTy { baseType = TInt }) <- HM.toList args
                                          ]
  pure $ HM.intersectionWith (,) args z3vars

buildCtxVars :: [FunSig] -> Z3 (HM.HashMap VarName (Ty, Z3VarName))
buildCtxVars sigs = do
  z3vars <- HM.fromList <$> mapM sequence [ (VarName funName, fmap Z3VarName $ mkStringSymbol funName >>= mkUninterpretedSort >>= mkFreshConst funName) -- TODO fun decl?
                                          | FunSig { .. } <- sigs
                                          ]
  pure $ HM.intersectionWith (,) tys z3vars
  where
    tys = HM.fromList [ (VarName funName, funTy) | FunSig { .. } <- sigs ]

type TypedTerm = TermT Ty

annotateTypes :: (MonadReader SolveEnvironment m) => Term -> m TypedTerm
annotateTypes (TName _ varName) = (`TName` varName) <$> askVarTy varName
annotateTypes (TInteger _ n) = pure $ TInteger (TyBase $ RefinedBaseTy TInt trueRefinement) n
annotateTypes (TBinOp _ t1 op t2) = do
  t1' <- annotateTypes t1
  t2' <- annotateTypes t2
  expectBaseTy TInt $ annotation t1'
  expectBaseTy TInt $ annotation t2'
  let resTy = case op of
                   BinOpPlus -> TInt
                   BinOpMinus -> TInt
                   BinOpGt -> TBool
                   BinOpLt -> TBool
  pure $ TBinOp (TyBase $ RefinedBaseTy resTy trueRefinement) t1' op t2'
annotateTypes TIfThenElse { .. } = do
  tcond' <- annotateTypes tcond
  expectBaseTy TBool $ annotation tcond'

  tthen' <- annotateTypes tthen
  telse' <- annotateTypes telse

  when (annotation tthen' /= annotation telse') $ error [i|Type mismatch between #{tthen} and #{telse}|]

  pure $ TIfThenElse (annotation tthen') tcond' tthen' telse'
annotateTypes (TApp _ t1 t2) = do
  t1' <- annotateTypes t1
  t2' <- annotateTypes t2
  resTy <- case annotation t1' of
                TyArrow ArrowTy { .. } -> do
                  when (stripRefinements domTy /= stripRefinements (annotation t2'))
                      $ error [i|Type mismatch: expected #{domTy}, got #{annotation t2'}|]
                  pure case piVarName of
                            Nothing -> codTy
                            Just varName -> substPi varName t2 codTy
                _ -> error [i|Expected arrow type, got #{annotation t1'}|]
  pure $ TApp resTy t1' t2'

-- TODO occurs check - rename whatever can be shadowed
substPi :: VarName -> Term -> Ty -> Ty
substPi srcName (TName _ dstName) = transformBi f
  where
    f (RArgVar var) | var == srcName = RArgVar dstName
    f (RArgVarLen var) | var == srcName = RArgVarLen dstName
    f arg = arg
substPi srcName (TInteger _ 0) = transformBi f
  where
    f (RArgVar var) | var == srcName = RArgZero
    f (RArgVarLen var) | var == srcName = RArgZero
    f arg = arg
substPi _ term = error [i|Unsupported substitution target: #{term}|]

-- TODO shall we generate more precise refinements here?
genTermsCstrs :: (MonadZ3 m, MonadReader SolveEnvironment m) => Z3VarName -> TypedTerm -> m AST
genTermsCstrs termVar (TName _ varName) = do
  z3Var <- askZ3VarName varName
  getZ3VarName termVar `mkEq` z3Var
genTermsCstrs termVar (TInteger _ n) = do
  num <- mkIntNum n
  getZ3VarName termVar `mkEq` num
genTermsCstrs termVar (TBinOp _ t1 op t2) = do
  (t1var, t1cstrs) <- mkVarCstrs "_linkVar_t1$" t1
  (t2var, t2cstrs) <- mkVarCstrs "_linkVar_t2$" t2
  bodyRes <- z3op t1var t2var
  bodyCstr <- getZ3VarName termVar `mkEq` bodyRes
  mkAnd [t1cstrs, t2cstrs, bodyCstr]
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
    thenEq <- getZ3VarName termVar `mkEq` thenVar
    mkAnd [thenCstrs, condVar, thenEq]
  elseClause <- do
    elseEq <- getZ3VarName termVar `mkEq` elseVar
    notCondVar <- mkNot condVar
    mkAnd [elseCstrs, notCondVar, elseEq]

  xor <- mkXor thenClause elseClause
  mkAnd [condCstrs, xor]
genTermsCstrs termVar (TApp resTy fun arg) = do
  subTyCstr <- case (annotation arg, annotation fun) of
                    (TyArrow _, _) -> error "TODO passing functions to functions is not supported yet" -- TODO
                    (TyBase rbtActual, TyArrow ArrowTy { domTy = TyBase rbtExpected }) -> do
                       ν <- Z3VarName <$> mkFreshIntVar "_∀_ν$"

                       actualCstr <- genRefinementCstrs rbtActual ν >>= mkAnd'
                       expectedCstr <- genRefinementCstrs rbtExpected ν >>= mkAnd'
                       implication <- mkImplies actualCstr expectedCstr

                       ν' <- toApp $ getZ3VarName ν
                       mkForallConst [] [ν'] implication
                    (_, _) -> error "Mismatched types (which should've been caught earlier though)"

  resCstr <- case resTy of
                  TyArrow _ -> mkTrue
                  TyBase rbt -> genRefinementCstrs rbt termVar >>= mkAnd

  mkAnd [resCstr, subTyCstr]

mkAnd' :: MonadZ3 m => [AST] -> m AST
mkAnd' [x] = pure x
mkAnd' xs = mkAnd xs

mkVarCstrs :: (MonadZ3 m, MonadReader SolveEnvironment m) => String -> TypedTerm -> m (AST, AST)
mkVarCstrs name term = do
  -- TODO not necessarily int
  var <- mkFreshIntVar name
  cstrs <- genTermsCstrs (Z3VarName var) term
  pure (var, cstrs)

expectBaseTy :: Monad m => BaseTy -> Ty -> m ()
expectBaseTy expected (TyBase RefinedBaseTy { .. }) | baseType == expected = pure ()
expectBaseTy expected ty = error [i|Expected #{expected}, got #{ty} instead|]

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
