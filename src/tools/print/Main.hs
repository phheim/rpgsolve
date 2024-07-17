module Main where

import RPG (parseGame, writeGame)

main :: IO ()
main = do
  input <- getContents
  case parseGame input of
    Left err -> fail err
    Right (game, wc) -> putStrLn (writeGame (game, wc))
