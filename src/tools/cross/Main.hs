{-# LANGUAGE LambdaCase #-}

module Main
  ( main
  ) where

import FOL
import RPG

import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map (empty, fromListWithKey, insert, toList)
import Data.Maybe (fromMaybe)
import Data.Set (cartesianProduct)
import qualified Data.Set as Set (map)
import System.Environment (getArgs)

gameProduct2 ::
     (Game, WinningCondition)
  -> (Game, WinningCondition)
  -> (Game, WinningCondition)
gameProduct2 (g1, wc1) (g2, wc2)
        -- add in- and outputs
 =
  let gA =
        foldl
          (\g v -> fromMaybe g $ addInput g v (ioType g2 ! v))
          emptyGame
          (inputs g2)
      gB =
        foldl
          (\g v -> fromMaybe g $ addInput g v (ioType g1 ! v))
          gA
          (inputs g1)
      gC =
        foldl
          (\g v ->
             fromMaybe g $
             addOutput g v (ioType g2 ! v) (v `elem` boundedCells g2))
          gB
          (outputs g2)
      gD =
        foldl
          (\g v ->
             fromMaybe g $
             addOutput g v (ioType g1 ! v) (v `elem` boundedCells g1))
          gC
          (outputs g1)
        -- add locations
      locProd = cartesianProduct (locations g1) (locations g2)
      (gE, mp) = foldl multLocs (gD, Map.empty) locProd
      gF = setInitial gE (mp ! (initial g1, initial g2))
        -- add invariants
      gG =
        foldl
          (\g (l1, l2) ->
             setInv g (mp ! (l1, l2)) (andf [g1 `inv` l1, g2 `inv` l2]))
          gF
          locProd
        -- add transitions 
      gH =
        foldl
          (\g (l1, l2) ->
             fromMaybe g $
             addTransition
               g
               (mp ! (l1, l2))
               (mergeTrans mp (tran g1 l1) (tran g2 l2)))
          gG
          locProd
        -- compute new winning condition
      wc =
        case (wc1, wc2) of
          (Safety s1, Safety s2) ->
            Safety $ Set.map (mp !) (cartesianProduct s1 s2)
          _ -> error "Only safety is allowed for now"
   in (gH, wc)
  where
    multLocs (g, mp) (l1, l2) =
      let (g', l) =
            addLocation
              g
              ((locationNames g1 ! l1) ++ "__" ++ (locationNames g2 ! l2))
       in (g', Map.insert (l1, l2) l mp)
    --
    mergeTrans mp t1 =
      \case
        TIf p tt tf -> TIf p (mergeTrans mp t1 tt) (mergeTrans mp t1 tf)
        TSys upds -> mergeTransH mp upds t1
    mergeTransH mp upd2 =
      \case
        TIf p tt tf -> TIf p (mergeTransH mp upd2 tt) (mergeTransH mp upd2 tf)
        TSys upd1 ->
          TSys
            [ (mergeUpds u1 u2, mp ! (l1, l2))
            | (u1, l1) <- upd1
            , (u2, l2) <- upd2
            ]
    mergeUpds u1 u2 =
      Map.fromListWithKey
        (\var old new ->
           case old of
             Var var' _ ->
               if var == var'
                 then new
                 else old
             _ -> old)
        (Map.toList u1 ++ Map.toList u2)

gameProduct :: [(Game, WinningCondition)] -> (Game, WinningCondition)
gameProduct =
  \case
    [] -> error "Cannot construct empty product"
    [gwc] -> gwc
    gwc:lr -> gameProduct2 gwc (gameProduct lr)

-- TODO: Make this cross-plattform!!
getDirPath :: String -> String
getDirPath = reverse . dropWhile (/= '/') . reverse

readGame :: String -> IO (Game, WinningCondition)
readGame path = do
  content <- readFile path
  case parseGame content of
    Left err -> fail err
    Right gwc -> return gwc

main :: IO ()
main = do
  crossFilePath <- head <$> getArgs
  subGameRelPaths <- (filter (not . null) <$> lines) <$> readFile crossFilePath
  let subGamePaths = map (getDirPath crossFilePath ++) subGameRelPaths
  games <- sequence (map readGame subGamePaths)
  putStrLn (writeGame (gameProduct games))
