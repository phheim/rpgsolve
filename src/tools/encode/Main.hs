{-# LANGUAGE LambdaCase #-}

module Main where

import System.Environment (getArgs)

import qualified MuCLP
import RPG
import qualified TSLT

main :: IO ()
main = do
  input <- getContents
  case parseGame input of
    Left err -> fail err
    Right (g, wc) -> do
      args <- getArgs
      case args of
        ["muclp"] -> putStrLn (MuCLP.convert g wc)
        ["tslt"] -> putStrLn (TSLT.convert g wc)
        _ -> error "Unkown arguments"
