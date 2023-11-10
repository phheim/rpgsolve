{-# LANGUAGE LambdaCase, FlexibleInstances #-}

module RPGSolve.Logging where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map (toList)
import Data.Set (Set)
import qualified Data.Set as Set (toList)

import Control.Monad (when)
import System.IO

import RPGSolve.Config

chainWith :: String -> [String] -> String
chainWith sep =
  \case
    [] -> ""
    [s] -> s
    s:sr -> s ++ sep ++ chainWith sep sr

class Loggable a where
  logMsg :: a -> String

instance Loggable String where
  logMsg = id

instance Loggable Word where
  logMsg = show

instance Loggable Bool where
  logMsg = show

instance Loggable a => Loggable (Set a) where
  logMsg s = "{" ++ chainWith ", " (fmap logMsg (Set.toList s)) ++ "}"

instance (Loggable a, Loggable b) => Loggable (Map a b) where
  logMsg s =
    "<" ++
    chainWith ", " ((\(a, b) -> logMsg a ++ "->" ++ logMsg b) <$> Map.toList s) ++
    ">"

writeOut :: CTX -> String -> IO ()
writeOut ctx msg =
  when (logging ctx) $
  hPutStrLn
    stderr
    (if cutLogs ctx
       then take 80 msg
       else msg)

lgMsg :: CTX -> String -> IO ()
lgMsg = writeOut

lg :: Loggable a => CTX -> String -> a -> IO ()
lg ctx field value = writeOut ctx (field ++ " " ++ logMsg value)

lgFirst :: Loggable a => CTX -> String -> a -> IO ()
lgFirst ctx name val = do
  lgStart ctx
  lg ctx name val

lgLast :: Loggable a => CTX -> String -> a -> IO ()
lgLast ctx name val = do
  lg ctx name val
  lgEnd ctx

lgStart :: CTX -> IO ()
lgStart ctx = writeOut ctx "{"

lgEnd :: CTX -> IO ()
lgEnd ctx = writeOut ctx "}"
