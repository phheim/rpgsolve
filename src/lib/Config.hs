{-# LANGUAGE LambdaCase #-}

module Config
  ( Config(..)
  , SMTSolver(..)
  , defaultConfig
  , setName
  , argumentParser
  , argumentDescription
  ) where

import Text.Read (readMaybe)

data SMTSolver
  = SMTSolverZ3
  | SMTSolverCVC5
  deriving (Eq, Ord, Show)

data Config =
  Config
    { logging :: Bool
    , logName :: String
    -- SMT solving
    , smtSolver :: SMTSolver
    , smtModelGenCommand :: String
    , smtQueryLogging :: Bool
    , smtSimplifyZ3Tacs :: [String]
    -- Game solving
    -- TODO
    }

defaultConfig :: Config
defaultConfig =
  Config
    { logging = True
    , logName = "[RPG]"
    , smtSolver = SMTSolverZ3
    , smtModelGenCommand =
        "(check-sat-using (and-then simplify (! default :macro-finder true)))"
    , smtQueryLogging = False
    , smtSimplifyZ3Tacs = z3Simplify
    }

setName :: String -> Config -> Config
setName name cfg = cfg {logName = "[" ++ name ++ "]"}

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

-- TODO: Move this somewhere else, it does not really fit
argumentParser :: [String] -> Either String Config
argumentParser = go defaultConfig
  where
    go cfg =
      \case
        [] -> pure cfg
        "--quiet":ar -> go (cfg {logging = False}) ar
        "--verbose":ar -> go (cfg {logging = True, smtQueryLogging = True}) ar
        "--solver-z3":ar -> go (cfg {smtSolver = SMTSolverZ3}) ar
        "--solver-cvc5":ar -> go (cfg {smtSolver = SMTSolverCVC5}) ar
        s:_ -> Left $ "found invalid argument: " ++ s
    --
    readNumber :: [String] -> Either String (Int, [String])
    readNumber =
      \case
        [] -> Left $ "expected number after last argument"
        a:ar ->
          case readMaybe a of
            Nothing -> Left $ "expected number, found " ++ a
            Just k -> Right (k, ar)

argumentDescription :: String
argumentDescription =
  unlines
    [ "--------------------------------------------------------------------------------"
    , " Generic options:"
    , "  --quiet       : disables logging (default: logging enable)"
    , "  --verbose     : enables verbose logging (default: verbose logging disabled)"
    , "  --solver-z3   : sets z3 as the smt-solver for all operations (default: yes)"
    , "  --solver-cvc5 : set cvc5 as the smt-solver for model queries (default: no)"
    , "                  remark: z3 is still needed for executing queries"
    ]
