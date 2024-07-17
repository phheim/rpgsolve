{-# LANGUAGE LambdaCase #-}

module Utils.Logging
  ( lg
  , strS
  , strM
  , strL
  , strP
  , strT
  ) where

import Config (Config(..))

import Data.Set (Set)
import qualified Data.Set as Set (toList)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map (toList)

import Control.Monad
import System.IO

inbetween :: a -> [a] -> [a]
inbetween sep =
  \case
    [] -> []
    [x] -> [x]
    x:xs -> x : sep : inbetween sep xs

strP :: (a -> String) -> (b -> String) -> (a, b) -> String
strP stra strb (a, b) = "(" ++ stra a ++ "," ++ strb b ++ ")"

strT :: (a -> String) -> (b -> String) -> (c -> String) -> (a, b, c) -> String
strT stra strb strc (a, b, c) =
  "(" ++ stra a ++ "," ++ strb b ++ "," ++ strc c ++ ")"

strL :: (a -> String) -> [a] -> String
strL str list = "[" ++ concat (inbetween ", " (str <$> list)) ++ "]"

strS :: Ord a => (a -> String) -> Set a -> String
strS str set = "{" ++ concat (inbetween ", " (str <$> Set.toList set)) ++ "}"

strM :: Ord k => (k -> String) -> (a -> String) -> Map k a -> String
strM strk stra mp =
  "{" ++
  concat
    (inbetween ", " ((\(k, a) -> strk k ++ "->" ++ stra a) <$> Map.toList mp)) ++
  "}"

lg :: Config -> [String] -> IO ()
lg cfg msgs =
  when (logging cfg) $ do
    let msgLines = filter (not . null) $ lines $ concatMap (++ " ") msgs ++ "\n"
    hPutStr stderr $ unlines $ map ((logName cfg ++ " ") ++) msgLines
