module Main where

import Parser (parseExpr)
import Typechecker (testTI)

main :: IO ()
main = do
  input <- getLine
  case parseExpr input of
    Left err -> putStrLn err
    Right e -> testTI e
