module Parser where

import Control.Monad (void)
import Data.Void
import Data.Bifunctor (first)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import AST
import Data.Text (Text)
import Data.Char (isDigit, isAlphaNum)
import qualified Data.Text as Text

parseExpr :: String -> Either String Exp
parseExpr = first show . runParser expParser ""

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space space1 lineCmnt blockCmnt
  where
    lineCmnt  = L.skipLineComment "//"
    blockCmnt = L.skipBlockComment "/*" "*/"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

integer :: Parser Integer
integer = lexeme L.decimal

rword :: String -> Parser ()
rword w = (lexeme . try) (string w *> notFollowedBy alphaNumChar)

rws :: [String] -- list of reserved words
rws = ["in","let"]

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p       = (:) <$> letterChar <*> many alphaNumChar
    check x = if x `elem` rws
                then fail $ "keyword " ++ show x ++ " cannot be an identifier"
                else return x

expParser :: Parser Exp
expParser = between sc eof expr

expr :: Parser Exp
expr = foldApps <$> some exprAtom

foldApps :: [Exp] -> Exp
foldApps [exp] = exp
foldApps xs = foldl1 EApp  xs

exprAtom :: Parser Exp
exprAtom = parens expr <|> let_ <|> abs_ <|> lit_ <|> EVar . Text.pack <$> identifier

let_ :: Parser Exp
let_ = do
  rword "let"
  var <- identifier
  void (symbol "=")
  expr1 <- expr
  rword "in"
  expr2 <- expr
  pure (ELet (Text.pack var) expr1 expr2)

abs_ :: Parser Exp
abs_ = do
  void (symbol "\\")
  var <- identifier
  (symbol "->")
  EAbs (Text.pack var) <$> expr

lit_ = ELit <$> (
  LInt <$> integer
  <|> (symbol "true" *> pure (LBool True))
  <|> (symbol "false" *> pure (LBool False))
  )
