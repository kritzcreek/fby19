{-# language OverloadedStrings #-}
module AST where

import Prelude hiding (unwords)

import Data.Text (Text, unwords)

data Exp
  = EVar Text
  | ELit Lit
  | EApp Exp Exp
  | EAbs Text Exp
  | ELet Text Exp Exp
  deriving (Eq, Ord, Show)

data Lit
  = LInt Integer
  | LBool Bool
  deriving (Eq, Ord, Show)

data Type
  = TVar Text
  | TInt
  | TBool
  | TFun Type Type
  deriving (Eq, Ord, Show)

data Scheme = Scheme [Text] Type

isFun :: Type -> Bool
isFun ty = case ty of
  TFun _ _ -> True
  _ -> False

prettyType :: Type -> Text
prettyType ty = case ty of
  TVar var -> var
  TInt -> "Int"
  TBool -> "Bool"
  TFun ty1 ty2 ->
    (if isFun ty1 then "(" <> prettyType ty1 <> ")" else prettyType ty1) 
    <> " -> " <> prettyType ty2

prettyScheme :: Scheme -> Text
prettyScheme (Scheme [] ty) = prettyType ty
prettyScheme (Scheme vars ty) = "forall " <> unwords vars <> ". " <> prettyType ty