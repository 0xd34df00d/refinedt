{-# LANGUAGE RecordWildCards, QuasiQuotes, LambdaCase #-}

module Toy.Language.Compiler
( compileFunSig
, compileFunDef
) where

import qualified Data.HashMap.Strict as HM
import Data.List
import Data.Maybe
import Data.String.Interpolate

import Toy.Language.EnvironmentUtils
import Toy.Language.Syntax.Decls
import Toy.Language.Syntax.Types

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
    unwrap var | var `HM.member` ctx = [i|fst #{getName var}|]
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
    funBodyStr = wrapping ctx (TyBase resType) $ parensUnwrapping ctx funBody
    ctx = buildTypesMapping [] argTypes

compileTerm :: Var2Ty -> TypedTerm -> String
compileTerm _ (TName _ var) = getName var
compileTerm ctx (TInteger ty n) = wrapping ctx ty $ show n
compileTerm ctx (TBinOp _ t1 op t2) = [i|(#{parensUnwrapping ctx t1} #{compileOp op} #{parensUnwrapping ctx t2})|]
compileTerm ctx (TApp _ t1 t2)
  | TyArrow ArrowTy { .. } <- annotation t1
  , let t2str = wrapping ctx domTy $ parensUnwrapping ctx t2 = [i|#{parens ctx t1} #{t2str}|]
  | otherwise = error "Unexpected function type"
compileTerm ctx TIfThenElse { .. } = [i|if #{compileTerm ctx tcond} then #{compileTermUnwrapping ctx tthen} else #{compileTermUnwrapping ctx telse}|]

withUnwrapping :: (Var2Ty -> TypedTerm -> String) -> Var2Ty -> TypedTerm -> String
withUnwrapping fun ctx t = unwrapping (annotation t) $ fun ctx t

parensUnwrapping :: Var2Ty -> TypedTerm -> String
parensUnwrapping = withUnwrapping parens

compileTermUnwrapping :: Var2Ty -> TypedTerm -> String
compileTermUnwrapping = withUnwrapping compileTerm

wrapping :: Var2Ty -> Ty -> String -> String
wrapping _ TyArrow {} str = str
wrapping ctx (TyBase RefinedBaseTy { .. }) str
  | baseTyRefinement == trueRefinement = str
  | otherwise = [i|(MkDPair {P = \\v => #{compileRefinement ctx baseTyRefinement}} (#{str}) smt)|]

unwrapping :: Ty -> String -> String
unwrapping TyArrow {} str = str
unwrapping (TyBase RefinedBaseTy { .. }) str
  | baseTyRefinement == trueRefinement = str
  | otherwise = [i|(fst (#{str}))|]

compileOp :: BinOp -> String
compileOp = \case BinOpPlus -> "+"
                  BinOpMinus -> "-"
                  BinOpGt -> ">"
                  BinOpLt -> "<"

parens :: Var2Ty -> TypedTerm -> String
parens ctx t | isSimple t = str
             | otherwise = "(" <> str <> ")"
  where
    str = compileTerm ctx t
    isSimple = \case TName {} -> True
                     TInteger {} -> True
                     _ -> False
