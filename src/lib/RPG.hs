module RPG
  ( Loc
  , Game(initial, inputs, outputs, ioType, locationNames, invariant,
     trans, predecessors, boundedCells)
  , WinningCondition(..)
  , Transition(..)
  -- Access
  , locationCnt
  , locations
  , tran
  , locName
  , inv
  , preds
  , predSet
  -- Construction
  , emptyGame
  , sameSymbolGame
  , addInput
  , addOutput
  , addLocation
  , addTransition
  , setInitial
  , setInv
  -- Other
  , succT
  , succs
  , mapTerms
  , cyclicIn
  , usedSymbols
  , pruneUnreachables
  , locNumber
  -- Reading / Writing
  , parseGame
  , writeGame
  --
  , simplifyRPG
  ) where

import RPGS.Game
import RPGS.Parser
import RPGS.Writer
