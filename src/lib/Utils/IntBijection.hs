{-# LANGUAGE LambdaCase #-}

module Utils.IntBijection
  ( Intable(toInt, fromInt)
  , IntBijection
  , empty
  , lkp
  , lkpRev
  , add
  ) where

import qualified Data.IntMap.Strict as IM (IntMap, empty, insert, lookup)
import qualified Data.Map.Strict as M (Map, empty, insert, lookup)

class Intable a where
  toInt :: a -> Int
  fromInt :: Int -> a

data IntBijection a b =
  IntBijection
    { cnt :: Int
    , mp :: IM.IntMap b
    , rv :: M.Map b Int
    }
  deriving (Eq, Ord, Show)

empty :: (Enum a, Ord b) => IntBijection a b
empty = IntBijection {cnt = 0, mp = IM.empty, rv = M.empty}

lkp :: (Enum a, Ord b) => a -> IntBijection a b -> Maybe b
lkp a bij = IM.lookup (fromEnum a) (mp bij)

lkpRev :: (Enum a, Ord b) => b -> IntBijection a b -> Maybe a
lkpRev b bij = toEnum <$> M.lookup b (rv bij)

add :: (Enum a, Ord b) => b -> IntBijection a b -> (a, IntBijection a b)
add b bij =
  case lkpRev b bij of
    Just n -> (n, bij)
    Nothing ->
      let n = cnt bij
       in ( toEnum n
          , IntBijection
              { cnt = n + 1
              , mp = IM.insert n b (mp bij)
              , rv = M.insert b n (rv bij)
              })
