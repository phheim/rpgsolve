{-# LANGUAGE LambdaCase #-}

module Main where

import RPG (parseGame)
import RPGSolve.Config
import RPGSolve.Solving (solve)

import System.Environment (getArgs)

validArgs :: [String] -> Bool
validArgs =
  all (`elem` ["disable-log", "disable-log-queries", "generate-program"])

parseArgs :: CTX -> [String] -> IO CTX
parseArgs ctx =
  \case
    [] -> return ctx
    "--disable-log":sr -> parseArgs (ctx {logging = False}) sr
    "--enable-full-log":sr -> parseArgs (ctx {cutLogs = False}) sr
    "--disable-query-log":sr -> parseArgs (ctx {logSMTQueries = False}) sr
    "--generate-program":sr -> parseArgs (ctx {generateProgram = True}) sr
    "--skolemize-only":sr -> parseArgs (ctx {skolemizeOnly = True}) sr
    "--gen-models-with":sr
      | null sr -> fail ("--gen-models-with expected an argument")
      | otherwise -> parseArgs (ctx {modelGenCommand = head sr}) (tail sr)
    "--smt-solver":sr
      | null sr -> fail ("--smt-solver expected an argument")
      | otherwise -> parseArgs (ctx {smtSolver = head sr}) (tail sr)
    "--smt-solver-arg":sr
      | null sr -> fail ("--smt-solver-arg expected an argument")
      | otherwise -> parseArgs (ctx {smtSolverArgs = head sr}) (tail sr)
    s:_ -> fail ("Invalid argument \"" ++ s ++ "\"")

main :: IO ()
main = do
  args <- getArgs
  ctx <- parseArgs defaultCTX args
  input <- getContents
  case parseGame input of
    Left err -> fail err
    Right (game, wc) -> solve ctx game wc
