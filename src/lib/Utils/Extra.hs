module Utils.Extra where

import Data.Set (Set)
import qualified Data.Set as Set (difference, empty, insert, singleton, union)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map (fromSet, insertWith)

import Utils.OpenList as OL

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM b t f = do
  b <- b
  if b
    then t
    else f

ifMP :: Monad m => m Bool -> a -> a -> m a
ifMP b t f = ifM b (return t) (return f)

ifMC :: Monad m => m Bool -> a -> m a -> m a
ifMC b t f = ifM b (return t) f

ifQuery :: Monad m => m (Bool, a) -> b -> b -> m (b, a)
ifQuery c t f = do
  (res, a) <- c
  if res
    then pure (t, a)
    else pure (f, a)

predecessorRelation :: Ord a => (a -> Set a) -> Set a -> Map a (Set a)
predecessorRelation succ base =
  let init = Map.fromSet (const Set.empty) base
   in foldl
        (\m src ->
           foldl
             (\m targ -> Map.insertWith Set.union targ (Set.singleton src) m)
             m
             (succ src))
        init
        base

reachables :: Ord a => (a -> Set a) -> Set a -> Set a
reachables succ = go Set.empty . OL.fromSet
  where
    go explored ol =
      case OL.pop ol of
        Nothing -> explored
        Just (a, ol)
          | a `elem` explored -> go explored ol
          | otherwise ->
            go
              (Set.insert a explored)
              (OL.push (succ a `Set.difference` explored) ol)

firstLine :: String -> String
firstLine str =
  case lines str of
    [] -> []
    s:_ -> s
