-------------------------------------------------------------------------------
-- | 
-- Module       :   Solving
--
-- 'Solving' implements the different solving techniques for the different
-- games. 
--
-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase, RecordWildCards #-}

-------------------------------------------------------------------------------
module RPGSolve.Solving
  ( solve
  ) where

-------------------------------------------------------------------------------
import Data.Map.Strict (Map, (!))

import Control.Monad (when)
import Data.Set (Set, difference)
import qualified Data.Set as Set (map, toList)

import FOL
import RPGS.Game
import RPGSolve.Attractor
import RPGSolve.CFG
import RPGSolve.Config
import RPGSolve.Logging
import RPGSolve.SMT (sat, smtLib2, valid)
import RPGSolve.SymbolicState

-------------------------------------------------------------------------------
-- Solving
-------------------------------------------------------------------------------
solve :: CTX -> Game -> WinningCondition -> IO ()
solve ctx g win = do
  (res, cfg) <-
    case win of
      Reachability ls -> solveReach ctx g ls
      Safety ls -> solveSafety ctx g ls
      Buechi ls -> solveBuechi ctx g ls
      CoBuechi ls -> solveCoBuechi ctx g ls
      Parity rank -> solveParity ctx g rank
  if res
    then do
      putStrLn "Realizable"
      when (generateProgram ctx) (process ctx cfg >>= putStrLn . printCFG g)
    else putStrLn "Unrealizable"

selectInv :: Game -> Set Loc -> SymSt
selectInv g locs =
  symSt
    g
    (\l ->
       if l `elem` locs
         then g `inv` l
         else false)

solveReach :: CTX -> Game -> Set Loc -> IO (Bool, CFG)
solveReach ctx g reach = do
  lgFirst ctx "Game type:" "Reachability"
  (a, cfg) <- attractorEx ctx Sys g (selectInv g reach)
  res <- valid (a `get` initial g)
  lgLast ctx "Game result:" res
  if res && generateProgram ctx
    then do
      cfg <- pure $ redirectGoal g (invSymSt g) cfg
      cfg <- pure $ setInitialCFG cfg (initial g)
      return (res, cfg)
    else return (res, emptyCFG)

foldLocs :: Set Loc -> (Loc -> CFG -> CFG) -> CFG -> CFG
foldLocs locs f cfg = foldl (flip f) cfg locs

solveSafety :: CTX -> Game -> Set Loc -> IO (Bool, CFG)
solveSafety ctx g safes = do
  lgFirst ctx "Game type:" "Safety"
  let envGoal = selectInv g (locations g `difference` safes)
  a <- attractor ctx Env g envGoal
  lgS ctx "Unsafe states:" g a
  lg ctx "Initial formula:" (smtLib2 (a `get` initial g))
  res <- not <$> sat (a `get` initial g)
  lgLast ctx "Game result:" res
  if res && generateProgram ctx
    then do
      cfg <-
        pure $
        foldLocs
          (locations g)
          (addUpd (mapSymSt neg a) g)
          (mkCFG (Set.toList (locations g)))
      cfg <- pure $ setInitialCFG cfg (initial g)
      return (res, cfg)
    else return (res, emptyCFG)

iterBuechi :: CTX -> Ply -> Game -> Set Loc -> IO (SymSt, SymSt)
iterBuechi ctx p g accept = iter (selectInv g accept) (0 :: Word)
  where
    iter fset i = do
      lg ctx "Iteration:" i
      lgS ctx "F_i" g fset
      bset <- attractor ctx p g fset
      lgS ctx "B_i" g bset
      cset <- cpreS ctx p g bset
      lgS ctx "C_i" g cset
      wset <- attractor ctx (opponent p) g (mapSymSt neg cset)
      lgS ctx "W_i+1" g wset
      fset' <- simplifySymSt ctx (fset `differenceS` wset)
      lgS ctx "F_i+1" g fset'
      fp <- impliesS fset fset'
      if fp
        then do
          lgS ctx "Fixed point:" g fset'
          return (wset, fset)
        else do
          lgS ctx "Recursion:" g fset'
          iter fset' (i + 1)

solveBuechi :: CTX -> Game -> Set Loc -> IO (Bool, CFG)
solveBuechi ctx g accepts = do
  lgFirst ctx "Game type:" "Buechi"
  lg ctx "Acceptings:" (Set.map (locationNames g !) accepts)
  (wenv, fset) <- iterBuechi ctx Sys g accepts
  lg ctx "Environment winning:" (smtLib2 (wenv `get` initial g))
  res <- not <$> sat (wenv `get` initial g)
  lgLast ctx "Game result:" res
  if res && generateProgram ctx
    then do
      (attr, cfg) <- attractorEx ctx Sys g fset
      cfg <- pure $ redirectGoal g attr cfg
      cfg <- pure $ setInitialCFG cfg (initial g)
      return (True, cfg)
    else return (res, emptyCFG)

solveCoBuechi :: CTX -> Game -> Set Loc -> IO (Bool, CFG)
solveCoBuechi ctx g stays = do
  lgFirst ctx "Game type:" "coBuechi"
  let rejects = locations g `difference` stays
  lg ctx "Rejects:" (Set.map (locationNames g !) rejects)
  (wsys, _) <- iterBuechi ctx Env g rejects
  lg ctx "System winning:" (smtLib2 (wsys `get` initial g))
  res <- valid (wsys `get` initial g)
  lgLast ctx "Game result:" res
  if res && generateProgram ctx
    then error "TODO"
    else return (res, emptyCFG)

solveParity :: CTX -> Game -> Map Loc Word -> IO (Bool, CFG)
solveParity = error "Old implementation was buggy, under construction."
-------------------------------------------------------------------------------
