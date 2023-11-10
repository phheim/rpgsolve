{-# LANGUAGE LambdaCase #-}

module RPGSolve.SMT
  ( satModelTO
  , sat
  , satTO
  , valid
  , implies
  , simplify
  , trySimplify
  , trySimplifyUF
  , smtLib2
  ) where

import Control.Monad (when)
import Data.Map ((!?))

import System.Exit (ExitCode(..))
import System.Process (readProcess, readProcessWithExitCode)

import FOL
import RPGSolve.Config
import RPGSolve.Logging
import SMTLib.Lexer
import SMTLib.Parser
import SMTLib.Writer

getSMTSolver :: CTX -> Maybe Word -> (String, String, [String])
getSMTSolver ctx mto =
  (preproc (modelGenCommand ctx), smtSolver ctx, words (smtSolverArgs ctx))
  where
    to = maybe maxBound id mto
    preproc =
      \case
        [] -> []
        '%':'1':sr -> show to ++ preproc sr
        '%':'2':sr -> show (to `div` 2) ++ preproc sr
        '%':'4':sr -> show (to `div` 4) ++ preproc sr
        '%':'8':sr -> show (to `div` 8) ++ preproc sr
        s:sr -> s : preproc sr

satModelTO :: CTX -> Maybe Word -> Term -> IO (Maybe (Maybe Model))
satModelTO ctx to f = do
  let (cmd, solver, args) = getSMTSolver ctx to
  let query = toSMTLib2 f ++ cmd ++ "(get-model)"
  when (logSMTQueries ctx) (lg ctx "Query:" query)
  out <- runTO to solver args query
  return
    (do res <- out
        case res of
          'u':'n':'s':'a':'t':_ -> return Nothing
          's':'a':'t':xr -> return (Just (extractModel (frees f) xr))
          _ -> error ("smt-solver returned unexpected: \"" ++ res ++ "\""))

sat :: Term -> IO Bool
sat = fmap (maybe undefined id) . satTO Nothing

satTO :: Maybe Word -> Term -> IO (Maybe Bool)
satTO to f = do
  let query = toSMTLib2 f ++ "(check-sat)"
  out <- runTO to "z3" ["--smt2", "--in"] query
  return
    (do res <- out
        case res of
          's':'a':'t':_ -> return True
          'u':'n':'s':'a':'t':_ -> return False
          _ -> error "smt-solver returned unexpected result")

valid :: Term -> IO Bool
valid f = not <$> sat (neg f)

implies :: Term -> Term -> IO Bool
implies f g = valid (f `impl` g)

readTransformZ3 :: (Symbol -> Maybe Sort) -> [Token] -> Term
readTransformZ3 ty =
  \case
    TLPar:TId "goals":TLPar:TId "goal":tr -> andf (readGoals tr)
    _ -> error "Assertion: Invalid pattern for goals"
  where
    readGoals =
      \case
        [] -> error "assertion: found [] before ')' while reading goals"
        TId (':':_):_:tr -> readGoals tr
        [TRPar, TRPar] -> []
        ts ->
          case parseTerm ty ts of
            Left err -> error ("Assertion: " ++ err)
            Right (f, tr) -> f : readGoals tr

z3TacticList :: [String] -> String
z3TacticList =
  \case
    [] -> error "assertion: non-empty tactic list not allowed"
    [t] -> t
    t:tr -> "(and-then " ++ t ++ " " ++ z3TacticList tr ++ ")"

z3Simplify :: [String]
z3Simplify =
  [ "simplify"
  , "propagate-ineqs"
  , "qe2"
  , "simplify"
  , "nnf"
  , "propagate-ineqs"
  , "ctx-solver-simplify"
  , "propagate-ineqs"
  , "unit-subsume-simplify"
  ]

simplify :: CTX -> Term -> IO Term
simplify ctx f = do
  let query = toSMTLib2 f ++ "(apply " ++ z3TacticList z3Simplify ++ ")"
  when (logSMTQueries ctx) (lg ctx "doSimplify:" query)
  res <- readProcess "z3" ["--smt2", "--in"] query
  return (readTransformZ3 (bindings f !?) (tokenize res))

trySimplify :: CTX -> Word -> Term -> IO (Maybe Term)
trySimplify ctx to f = do
  let query = toSMTLib2 f ++ "(apply " ++ z3TacticList z3Simplify ++ ")"
  when (logSMTQueries ctx) (lg ctx "trySimplify:" query)
  res <-
    readProcess "z3" ["timeout=" ++ show (1000 * to), "--smt2", "--in"] query
  case res of
    '(':'e':'r':'r':_ -> return Nothing -- TODO: This is a bit hacky!
    _ -> return (Just (readTransformZ3 (bindings f !?) (tokenize res)))

z3SimplifyUF :: [String]
z3SimplifyUF = ["simplify", "propagate-ineqs", "qe", "simplify"]

trySimplifyUF :: CTX -> Word -> Term -> IO (Maybe Term)
trySimplifyUF ctx to f = do
  let query = toSMTLib2 f ++ "(apply " ++ z3TacticList z3SimplifyUF ++ ")"
  when (logSMTQueries ctx) (lg ctx "trySimplifyUF:" query)
  res <-
    readProcess "z3" ["timeout=" ++ show (1000 * to), "--smt2", "--in"] query
  case res of
    '(':'e':'r':'r':_ -> return Nothing -- TODO: This is a bit hacky!
    _ -> return (Just (readTransformZ3 (bindings f !?) (tokenize res)))

runTO :: Maybe Word -> String -> [String] -> String -> IO (Maybe String)
runTO to cmd args input =
  case to of
    Nothing -> do
      (_, res, _) <- readProcessWithExitCode cmd args input
      return (Just res)
    Just n -> do
      (ext, res, _) <-
        readProcessWithExitCode "timeout" (show n : cmd : args) input
      case ext of
        ExitSuccess -> return (Just res)
        ExitFailure n
          | n == 124 -> return Nothing
          | otherwise -> return (Just res)
