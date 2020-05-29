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

compileFunDef :: FunSig -> TypedFunDef -> String
compileFunDef sig def@FunDef { .. } = [i|#{funName} #{unwords funArgsNames} = #{funBodyStr}|]
  where
    funArgsNames = getName <$> funArgs
    resType = snd $ funTypesMapping sig def
    funBodyStr = wrapping (TyBase resType) $ compileUnwrapping funBody

compileTerm :: TypedTerm -> String
compileTerm (TName _ var) = getName var
compileTerm (TInteger ty n) = wrapping ty $ show n
compileTerm (TBinOp _ t1 op t2) = [i|(#{compileUnwrapping t1} #{compileOp op} #{compileUnwrapping t2})|]
compileTerm (TApp _ t1 t2)
  | TyArrow ArrowTy { .. } <- annotation t1
  , let t2str = wrapping domTy $ compileUnwrapping t2 = [i|#{parens t1} #{t2str}|]
  | otherwise = error "Unexpected function type"
compileTerm TIfThenElse { .. } = [i|if #{compileTerm tcond} then #{compileTerm tthen} else #{compileTerm telse}|]

compileUnwrapping :: TypedTerm -> String
compileUnwrapping t = unwrapping (annotation t) $ parens t

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
