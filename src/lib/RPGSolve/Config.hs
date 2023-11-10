module RPGSolve.Config where

data CTX =
  CTX
    { logging :: Bool
    , logSMTQueries :: Bool
    , cutLogs :: Bool
    , generateProgram :: Bool
    , skolemizeOnly :: Bool
    , modelGenCommand :: String
    , smtSolver :: String
    , smtSolverArgs :: String
    }

defaultCTX :: CTX
defaultCTX =
  CTX
    { logging = True
    , generateProgram = False
    , logSMTQueries = True
    , cutLogs = True
    , skolemizeOnly = False
    , modelGenCommand =
        "(check-sat-using (and-then simplify (! default :macro-finder true)))"
    , smtSolver = "z3"
    , smtSolverArgs = "-smt2 -in"
    }
