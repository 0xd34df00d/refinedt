{-# LANGUAGE RecordWildCards, QuasiQuotes, LambdaCase #-}

module Toy.Language.Compiler
( compileFunSig
, compileFunDef
, compileDecls
) where

import qualified Data.HashMap.Strict as HM
import Data.List
import Data.Maybe
import Data.String.Interpolate

import Toy.Language.BasicTC
import Toy.Language.EnvironmentUtils
import Toy.Language.Syntax.Decls
import Toy.Language.Syntax.Types

compileDecl :: [FunSig] -> Decl -> String
compileDecl ctx Decl { .. } = sig' <> fromMaybe "" def'
  where
    sig' = compileFunSig declSig <> "\n"
    def' = (<> "\n") . compileFunDef declSig . annotateFunDef ctx declSig <$> declDef

compileDecls :: [Decl] -> String
compileDecls decls = unlines $ zipWith compileDecl (inits sigs) decls
  where
    sigs = declSig <$> decls

-- TODO need the surrounding context
compileFunSig :: FunSig -> String
compileFunSig FunSig { .. } = [i|#{funName} : #{compileTy funTy}|]

compileTy :: Ty -> String
compileTy = go mempty
  where
    go ctx (TyBase RefinedBaseTy { .. })
      | baseTyRefinement == trueRefinement = compileBaseTy baseType
      | otherwise = [i|(v : #{compileBaseTy baseType} ** #{compileRefinement ctx baseTyRefinement})|]
    go ctx (TyArrow ArrowTy { .. })
      | isBaseTy domTy || isJust piVarName = [i|#{lhs} -> #{go ctx' codTy}|]
      | otherwise = [i|(#{lhs}) -> #{go ctx' codTy}|]
      where
        ctx' | Just varName <- piVarName = HM.insert varName domTy ctx
             | otherwise = ctx
        lhs | Just name <- piVarName = [i|(#{getName name} : #{go ctx domTy})|]
            | otherwise = compileTy domTy

compileRefinement :: Var2Ty -> Refinement -> String
compileRefinement ctx refinement =
  case conjuncts refinement of
       [] -> "()"
       [conj] -> compileAR ctx conj
       conjs -> "(" <> intercalate ", " (compileAR ctx <$> conjs) <> ")"

compileAR :: Var2Ty -> AtomicRefinement -> String
compileAR ctx (AR op arg) = [i|v #{opStr} #{argStr} = True|]
  where
    opStr = case op of
                 ROpLt -> "<"
                 ROpLeq -> "<="
                 ROpEq -> "=="
                 ROpNEq -> "/="
                 ROpGt -> ">"
                 ROpGeq -> ">="
    argStr = case arg of
                  RArgInt n -> show n
                  RArgVar var -> unwrap var
                  RArgVarLen var -> "intLength " <> unwrap var
    unwrap var | Just varTy <- HM.lookup var ctx
               , isJust $ tyRefinement varTy = [i|fst #{getName var}|]
               | otherwise = getName var

compileBaseTy :: BaseTy -> String
compileBaseTy TBool = "Bool"
compileBaseTy TInt = "Int"
compileBaseTy TIntList = "List Int"

-- TODO need the surrounding context
compileFunDef :: FunSig -> TypedFunDef -> String
compileFunDef sig def@FunDef { .. } = [i|#{funName} #{unwords funArgsNames} = #{funBodyStr}|]
  where
    funArgsNames = getName <$> funArgs
    (argTypes, resType) = funTypesMapping sig def
    funBodyStr = wrapping ctx (TyBase resType) $ unwrapping ctx funBody
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
  | Just refinement <- tyRefinement ty = [i|MkDPair {p = \\v => #{compileRefinement ctx refinement}} #{parens str} smt|]
  | otherwise = str

unwrapStr :: Ty -> String -> String
unwrapStr ty str
  | isJust $ tyRefinement ty = [i|fst #{parens str}|]
  | otherwise = str

etaExpand :: Var2Ty -> Ty -> ArrowTy -> TypedTerm -> String
etaExpand outerCtx expectedTy funTy fun = [i|\\#{lamArgs} => #{rhsTermStr}|]
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

compileOp :: BinOp -> String
compileOp = \case BinOpPlus -> "+"
                  BinOpMinus -> "-"
                  BinOpGt -> ">"
                  BinOpLt -> "<"

parens :: String -> String
parens str
  | ' ' `notElem` str = str
  | head str == '(' && last str == ')' && isBalanced (init $ tail str) = str
  | otherwise = "(" <> str <> ")"
  where
    isBalanced = (\(n, b) -> b && n == 0) . foldl' f (0 :: Int, True)
    f (0, _) ')' = (0, False)
    f (n, b) '(' = (n + 1, b)
    f (n, b) ')' = (n - 1, b)
    f (n, b) _ = (n, b)
