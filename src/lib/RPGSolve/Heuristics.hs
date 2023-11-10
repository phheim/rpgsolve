module RPGSolve.Heuristics where

import Data.List (genericReplicate)

-- This constant is a bit vodoo, its size depends on the acceperation/loop size
-- and size of the game combined in order to ensure sufficent 
-- information proagation. We picked 4 as a reasonable choice, as 
-- we usually have small loops. We might use a more complex heuristic to compute
-- this in general.
accelerationDist :: Word
accelerationDist = 4

visits2accel :: Word -> Bool
visits2accel k = (k >= accelerationDist) && (k `mod` accelerationDist == 0)

limit2skolemNum :: Word -> Bool
limit2skolemNum k = k `mod` 8 == 0

limit2depth :: Word -> Word
limit2depth k
  | k <= accelerationDist = 0 -- Try once without nesting
  | otherwise = (k `div` (10 * accelerationDist)) + 1

limit2to :: Word -> Word
limit2to k = k * k

limit2toextract :: Word -> Word
limit2toextract k = 4 * limit2to k

--TODO: Add bound by number of cells!
templateConfig :: Word -> (Integer, [Integer])
templateConfig limit =
  let dis = accelerationDist * accelerationDist
   in (2 + toInteger (limit `div` dis), genericReplicate (limit `div` dis) 2)
