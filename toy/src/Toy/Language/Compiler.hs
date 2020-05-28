{-# LANGUAGE RecordWildCards, QuasiQuotes, LambdaCase #-}

module Toy.Language.Compiler
( compileFunSig
, compileFunDef
) where

import Data.List
import Data.Maybe
import Data.String.Interpolate

import Toy.Language.EnvironmentUtils
import Toy.Language.Syntax.Decls
import Toy.Language.Syntax.Types

compileFunSig :: FunSig -> String
compileFunSig FunSig { .. } = [i|#{funName} : #{compileTy funTy}|]

compileTy :: Ty -> String
compileTy (TyBase RefinedBaseTy { .. })
  | baseTyRefinement == trueRefinement = compileBaseTy baseType
  | otherwise = [i|(v : #{compileBaseTy baseType} ** #{compileRefinement baseTyRefinement})|]
compileTy (TyArrow ArrowTy { .. })
  | isBaseTy domTy || isJust piVarName = [i|#{lhs} -> #{compileTy codTy}|]
  | otherwise = [i|(#{lhs}) -> #{compileTy codTy}|]
  where
    lhs | Just name <- piVarName = [i|(#{getName name} : #{compileTy domTy})|]
        | otherwise = compileTy domTy

compileRefinement :: Refinement -> String
compileRefinement refinement =
  case conjuncts refinement of
       [] -> "()"
       [conj] -> compileAR conj
       conjs -> "(" <> intercalate ", " (compileAR <$> conjs) <> ")"

compileAR :: AtomicRefinement -> String
compileAR (AR op arg) = [i|v #{opStr} #{argStr} = True|]
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
                  RArgVar var -> getName var
                  RArgVarLen var -> "intLength " <> getName var

compileBaseTy :: BaseTy -> String
compileBaseTy TBool = "Bool"
compileBaseTy TInt = "Int"
compileBaseTy TIntList = "List Int"

compileFunDef :: FunSig -> TypedFunDef -> String
compileFunDef sig def@FunDef { .. } = [i|#{funName} #{unwords funArgsNames} = #{funBodyStr}|]
  where
    funArgsNames = getName <$> funArgs
    resType = snd $ funTypesMapping sig def
    funBodyStr = wrapping (TyBase resType) $ unwrapping (annotation funBody) $ compileTerm funBody

compileTerm :: TypedTerm -> String
compileTerm (TName _ var) = getName var
compileTerm (TInteger ty n) = wrapping ty $ show n
compileTerm (TBinOp _ t1 op t2) = [i|(#{compileTerm t1} #{compileOp op} #{compileTerm t2})|]
compileTerm (TApp _ t1 t2)
  | TyArrow ArrowTy { .. } <- annotation t1
  , let t2str = wrapping domTy $ unwrapping (annotation t2) $ parens t2 = [i|#{parens t1} #{t2str}|]
  | otherwise = error "Unexpected function type"
compileTerm TIfThenElse { .. } = [i|if #{compileTerm tcond} then #{compileTerm tthen} else #{compileTerm telse}|]

wrapping :: Ty -> String -> String
wrapping TyArrow {} str = str
wrapping (TyBase RefinedBaseTy { .. }) str
  | baseTyRefinement == trueRefinement = str
  | otherwise = [i|(MkDPair {P = \\v => #{compileRefinement baseTyRefinement}} (#{str}) (believe_me ()))|]

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

parens :: TypedTerm -> String
parens t | isSimple t = str
         | otherwise = "(" <> str <> ")"
  where
    str = compileTerm t
    isSimple = \case TName {} -> True
                     TInteger {} -> True
                     _ -> False
