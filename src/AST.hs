module AST where

import Data.Text (Text)

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
