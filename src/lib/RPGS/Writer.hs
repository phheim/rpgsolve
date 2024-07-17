{-# LANGUAGE LambdaCase #-}

module RPGS.Writer
  ( writeGame
  ) where

import FOL
import RPGS.Game
import SMTLib.Writer (smtLib2)

import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map (toList)
import Data.Set (toList)

writeSort :: Sort -> String
writeSort =
  \case
    SInt -> "Int"
    SBool -> "Bool"
    SReal -> "Real"
    SFunc _ _ -> error $ "function sort not allowed for game writing"

writeWC :: WinningCondition -> String
writeWC =
  \case
    Safety _ -> "Safety"
    Reachability _ -> "Reach"
    Buechi _ -> "Buechi"
    CoBuechi _ -> "coBuechi"
    Parity _ -> "Parity"

writeTrans :: (Loc -> String) -> Transition -> String
writeTrans wl =
  \case
    TIf p tt tf ->
      "if " ++
      smtLib2 p ++ " then " ++ writeTrans wl tt ++ " else " ++ writeTrans wl tf
    TSys choices -> "sys( " ++ concatMap wSys choices ++ ")"
  where
    wUpd (s, t) = "(" ++ s ++ " " ++ smtLib2 t ++ ")"
    wSys (upd, l) =
      "(" ++ concatMap wUpd (Map.toList upd) ++ ") " ++ wl l ++ " "

writeGame :: (Game, WinningCondition) -> String
writeGame (g, wc) =
  unlines $
  ["type " ++ writeWC wc, ""] ++
  ["output " ++ o ++ " " ++ wty o | o <- outputs g] ++
  ["input " ++ i ++ " " ++ wty i | i <- inputs g] ++
  [""] ++
  ["loc " ++ ln l ++ " " ++ ac l ++ " ; " ++ show l | l <- locl] ++
  [""] ++
  ["init " ++ ln (initial g)] ++
  [""] ++ ["trans " ++ ln l ++ " " ++ writeTrans ln (trans g ! l) | l <- locl]
  where
    locl = toList (locations g)
    wty x = " " ++ writeSort (ioType g ! x)
    ln l = "l" ++ show (locNumber g l) ++ "_" ++ (locationNames g ! l)
    em s l
      | l `elem` s = "1"
      | otherwise = "0"
    ac =
      case wc of
        Safety s -> em s
        Reachability s -> em s
        Buechi s -> em s
        CoBuechi s -> em s
        Parity rank -> show . (rank !)
