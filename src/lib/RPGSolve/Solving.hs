-------------------------------------------------------------------------------
-- | 
-- Module       :   Solving
--
-- 'Solving' implements the different solving techniques for the different
-- games. 
--
-------------------------------------------------------------------------------
module RPGSolve.Solving
  ( solve
  , solveCache
  ) where

-------------------------------------------------------------------------------
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map (toList)

import Control.Monad (when)
import Data.Set (Set, difference)
import qualified Data.Set as Set (map, toList)

import FOL
import RPG
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
      Reachability ls -> solveReach ctx [] g ls
      Safety ls -> solveSafety ctx [] g ls
      Buechi ls -> solveBuechi ctx [] g ls
      CoBuechi ls -> solveCoBuechi ctx [] g ls
      Parity rank -> solveParity ctx [] g rank
  if res
    then do
      putStrLn "Realizable"
      when (generateProgram ctx) (process ctx cfg >>= putStrLn . printCFG g)
    else putStrLn "Unrealizable"

solveCache :: CTX -> Cache -> Game -> WinningCondition -> IO Bool
solveCache ctx cache g win = do
  ctx <- pure $ ctx {generateProgram = False}
  (res, _) <-
    case win of
      Reachability ls -> solveReach ctx cache g ls
      Safety ls -> solveSafety ctx cache g ls
      Buechi ls -> solveBuechi ctx cache g ls
      CoBuechi ls -> solveCoBuechi ctx cache g ls
      Parity rank -> solveParity ctx cache g rank
  return res

selectInv :: Game -> Set Loc -> SymSt
selectInv g locs =
  symSt
    g
    (\l ->
       if l `elem` locs
         then g `inv` l
         else false)

solveReach :: CTX -> Cache -> Game -> Set Loc -> IO (Bool, CFG)
solveReach ctx cache g reach = do
  lgFirst ctx "Game type:" "Reachability"
  (a, cfg) <- attractorEx ctx cache Sys g (selectInv g reach)
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

solveSafety :: CTX -> Cache -> Game -> Set Loc -> IO (Bool, CFG)
solveSafety ctx cache g safes = do
  lgFirst ctx "Game type:" "Safety"
  let envGoal = selectInv g (locations g `difference` safes)
  a <- attractorCache ctx Env g cache envGoal
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

iterBuechi :: CTX -> Cache -> Ply -> Game -> Set Loc -> IO (SymSt, SymSt)
iterBuechi ctx cache p g accept = iter (selectInv g accept) (0 :: Word)
  where
    iter fset i = do
      lg ctx "Iteration:" i
      lgS ctx "F_i" g fset
      bset <- attractorCache ctx p g cache fset
      lgS ctx "B_i" g bset
      cset <- cpreS ctx p g bset
      lgS ctx "C_i" g cset
      wset <- attractorCache ctx (opponent p) g cache (mapSymSt neg cset)
      lgS ctx "W_i+1" g wset
      fset' <- simplifySymSt ctx (fset `differenceS` wset)
      lgS ctx "F_i+1" g fset'
      fp <- impliesS fset fset'
      if fp
        then do
          lgS ctx "Fixed point:" g fset'
          return (wset, fset)
        else do
          earlyStop <-
            case p of
              Sys -> sat (wset `get` initial g)
              Env -> valid (wset `get` initial g)
          if False && earlyStop
            then do
              lgMsg ctx "Early stop"
              return (wset, fset)
            else do
              lgS ctx "Recursion:" g fset'
              iter fset' (i + 1)

solveBuechi :: CTX -> Cache -> Game -> Set Loc -> IO (Bool, CFG)
solveBuechi ctx cache g accepts = do
  lgFirst ctx "Game type:" "Buechi"
  lg ctx "Acceptings:" (Set.map (locationNames g !) accepts)
  (wenv, fset) <- iterBuechi ctx cache Sys g accepts
  lg ctx "Environment winning:" (smtLib2 (wenv `get` initial g))
  res <- not <$> sat (wenv `get` initial g)
  lgLast ctx "Game result:" res
  if res && generateProgram ctx
    then do
      (attr, cfg) <- attractorEx ctx cache Sys g fset
      cfg <- pure $ redirectGoal g attr cfg
      cfg <- pure $ setInitialCFG cfg (initial g)
      return (True, cfg)
    else return (res, emptyCFG)

solveCoBuechi :: CTX -> Cache -> Game -> Set Loc -> IO (Bool, CFG)
solveCoBuechi ctx cache g stays = do
  lgFirst ctx "Game type:" "coBuechi"
  let rejects = locations g `difference` stays
  lg ctx "Rejects:" (Set.map (locationNames g !) rejects)
  (wsys, _) <- iterBuechi ctx cache Env g rejects
  lg ctx "System winning:" (smtLib2 (wsys `get` initial g))
  res <- valid (wsys `get` initial g)
  lgLast ctx "Game result:" res
  if res && generateProgram ctx
    then error "TODO"
    else return (res, emptyCFG)

solveParity :: CTX -> Cache -> Game -> Map Loc Word -> IO (Bool, CFG)
solveParity ctx cache g colors
    -- TODO: add logging
 = do
  (_, wsys) <- zielonka g
  res <- valid (wsys `get` initial g)
  if res && generateProgram ctx
    then error "TODO"
    else return (res, emptyCFG)
  where
    colorList = Map.toList colors
    --
    maxColor :: Game -> Word
    maxColor g = maximum [col | (l, col) <- colorList, inv g l /= false]
    --
    colorPlayer :: Word -> Ply
    colorPlayer col
      | col `mod` 2 == 0 = Env
      | otherwise = Sys
    --
    playerSet Env = fst
    playerSet Sys = snd
    mkPlSet Env (wply, wopp) = (wply, wopp)
    mkPlSet Sys (wply, wopp) = (wopp, wply)
    removeFromGame symst g = do
      newInv <- simplifySymSt ctx (invSymSt g `differenceS` symst)
      pure $ foldl (\g l -> setInv g l (newInv `get` l)) g (locations g)
    --
    zielonka :: Game -> IO (SymSt, SymSt)
    zielonka g
     -- TODO: Check that this is really needed
      | isEmptySt (invSymSt g) = pure (emptySt g, emptySt g)
      | otherwise = do
        let color = maxColor g
        let player = colorPlayer color
        let opp = opponent player
        let targ =
              symSt
                g
                (\l ->
                   if colors ! l == color
                     then inv g l
                     else false)
        let full = invSymSt g
        lgS ctx "Parity:" g full
        lg ctx "Parity color" color
        lgS ctx "Parity target:" g targ
        aset <- attractorCache ctx player g cache targ
        eqiv <- impliesS full aset
        if eqiv
          then do
            lgMsg ctx "Parity return 0"
            pure $ mkPlSet player (full, emptySt g)
          else do
            g' <- removeFromGame aset g
            lgMsg ctx "Parity Recurse 1"
            winOp' <- playerSet opp <$> zielonka g'
            winOp' <- simplifySymSt ctx winOp'
            if isEmptySt winOp'
              then do
                lgMsg ctx "Parity return 1"
                pure $ mkPlSet player (full, emptySt g)
              else do
                remove <- attractorCache ctx opp g cache winOp'
                g'' <- removeFromGame remove g
                lgMsg ctx "Parity Recurse 2"
                winPl'' <- playerSet player <$> zielonka g''
                lgMsg ctx "Parity return 2"
                pure $ mkPlSet player (winPl'', full `differenceS` winPl'')
-------------------------------------------------------------------------------
