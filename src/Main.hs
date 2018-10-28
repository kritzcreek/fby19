module Main where

import Data.Foldable (for_)
import Parser (parseExpr)
import Typechecker (testTI)

main :: IO ()
main = do
  inputs <- getContents
  for_ (lines inputs) $ \input -> case parseExpr input of
    Left err -> putStrLn err
    Right e -> testTI e
