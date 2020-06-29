{-# LANGUAGE RecordWildCards, QuasiQuotes, LambdaCase #-}

module Toy.Language.Compiler
( compileFunSig
, compileFunDef
, compileDecls
) where

import qualified Data.HashMap.Strict as HM
import Control.Monad
import Control.Monad.Reader
import Data.List
import Data.Maybe
import Data.String.Interpolate

import Misc.Util
import Toy.Language.BasicTC
import Toy.Language.EnvironmentUtils
import Toy.Language.Solver
import Toy.Language.Syntax

compileDecl :: [FunSig] -> Decl -> IO String
compileDecl ctx Decl { .. }
  | Just def <- declDef = do
      let typedDef = annotateFunDef ctx declSig def
      let qdef = genQueriesFunDef declSig typedDef
      (res, solvedFunDef) <- solveDef declSig qdef
      case res of
           Correct -> pure $ sig' <> compileFunDef declSig solvedFunDef
           _ -> error "solve failed"
  | otherwise = pure sig'
  where
    sig' = compileFunSig declSig <> "\n"

compileDecls :: [Decl] -> IO String
compileDecls decls = unlines <$> zipWithM compileDecl (inits sigs) decls
  where
    sigs = declSig <$> decls

-- TODO need the surrounding context
compileFunSig :: FunSig -> String
compileFunSig FunSig { .. } = [i|#{funName} : #{compileTy funTy}|]

compileTy :: Ty -> String
compileTy = go mempty
  where
    go ctx (TyBase RefinedBaseTy { .. })
      | Just refinement <- baseTyRefinement = [i|(v : #{compileBaseTy baseType} ** #{compileRefinement ctx baseType refinement})|]
      | otherwise = compileBaseTy baseType
    go ctx (TyArrow ArrowTy { .. })
      | isBaseTy domTy || isJust piVarName = [i|#{lhs} -> #{go ctx' codTy}|]
      | otherwise = [i|(#{lhs}) -> #{go ctx' codTy}|]
      where
        ctx' | Just varName <- piVarName = HM.insert varName domTy ctx
             | otherwise = ctx
        lhs | Just name <- piVarName = [i|(#{getName name} : #{go ctx domTy})|]
            | otherwise = go ctx domTy

compileRefinement :: Var2Ty -> BaseTy -> Refinement -> String
compileRefinement ctx baseTy refinement =
  case conjuncts refinement of
       [] -> "()"
       [conj] -> compileAR ctx' conj
       conjs -> "(" <> intercalate ", " (compileAR ctx' <$> conjs) <> ")"
  where
    ctx' = HM.insert (subjectVar refinement) (TyBase $ RefinedBaseTy baseTy Nothing) ctx

compileAR :: Var2Ty -> AtomicRefinement -> String
compileAR ctx (AR term) = [i|#{compileTerm ctx typedTerm} = True|]
  where
    typedTerm = runReader (annotateTypes term) ctx

compileBaseTy :: BaseTy -> String
compileBaseTy TBool = "Bool"
compileBaseTy TInt = "Int"
compileBaseTy TIntList = "List Int"

-- TODO need the surrounding context
compileFunDef :: FunSig -> VCFunDef SolveRes -> String
compileFunDef sig def@FunDef { .. } = [i|#{funName} #{unwords funArgsNames} = #{funBodyStr}|]
  where
    funArgsNames = getName <$> funArgs
    (argTypes, resType) = funTypesMapping sig def
    funBodyStr = wrapping ctx (TyBase resType) $ unwrapping ctx $ tyAnn . refAnn <$> funBody
    ctx = buildTypesMapping [] argTypes

compileTerm :: Var2Ty -> TypedTerm -> String
compileTerm _ (TName _ var) = getName var
compileTerm ctx (TInteger ty n) = wrapping ctx ty $ show n
compileTerm ctx (TBinOp _ t1 op t2) = [i|(#{unwrapping ctx t1} #{compileOp op} #{unwrapping ctx t2})|]
compileTerm ctx (TApp _ t1 t2)
  | TyArrow ArrowTy { .. } <- annotation t1 =
      let t2str = case annotation t2 of
                       TyBase {} -> wrapping ctx domTy $ unwrapping ctx t2
                       TyArrow arr -> etaExpand ctx domTy arr t2
       in [i|#{parens $ compileTerm ctx t1} #{parens t2str}|]
  | otherwise = error "Unexpected function type"
compileTerm ctx TIfThenElse { .. } = [i|if #{compileTerm ctx tcond} then #{unwrapping ctx tthen} else #{unwrapping ctx telse}|]

unwrapping :: Var2Ty -> TypedTerm -> String
unwrapping ctx t = unwrapStr (annotation t) $ compileTerm ctx t

wrapping :: Var2Ty -> Ty -> String -> String
wrapping ctx ty str
  | TyBase RefinedBaseTy { .. } <- ty
  , Just refinement <- baseTyRefinement = [i|MkDPair {p = \\v => #{compileRefinement ctx baseType refinement}} #{parens str} smt|]
  | otherwise = str

unwrapStr :: Ty -> String -> String
unwrapStr ty str
  | isJust $ tyRefinement ty = [i|fst #{parens str}|]
  | otherwise = str

etaExpand :: Var2Ty -> Ty -> ArrowTy -> TypedTerm -> String
etaExpand outerCtx calleeFunTy funTy fun = [i|\\#{lamArgs} => #{rhsTermStr}|]
  where
    lamArgs = intercalate ", " $ getName <$> reverse lamBinders
    rhsTermStr = wrapping outerCtx expectedTy $ unwrapping subCtx rhsTerm

    (subCtx, lamBinders, rhsTerm) = buildApp (outerCtx, [], fun) funTy
    buildApp (ctx, binders, term) ArrowTy { .. }
      | TyArrow arr <- codTy = buildApp next arr
      | otherwise = next
      where
        next = (ctx', binders', term')
        ctx' = HM.insert name domTy ctx
        binders' = name : binders
        term' = TApp codTy term (TName domTy name)
        name = VarName $ "narg" <> show (length ctx)

    expectedTy = retTy calleeFunTy
    retTy (TyArrow ArrowTy { .. }) = retTy codTy
    retTy baseTy = baseTy

compileOp :: BinOp -> String
compileOp = \case BinOpPlus -> "+"
                  BinOpMinus -> "-"
                  BinOpGt -> ">"
                  BinOpGeq -> ">="
                  BinOpEq -> "=="
                  BinOpNEq -> "/="
                  BinOpLt -> "<"
                  BinOpLeq -> "<="
