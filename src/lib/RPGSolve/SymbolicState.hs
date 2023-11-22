{-# LANGUAGE LambdaCase, RecordWildCards #-}

module RPGSolve.SymbolicState where

-------------------------------------------------------------------------------
import Data.Map.Strict (Map, (!), (!?), fromSet, keys, mapKeys, mapWithKey)
import qualified Data.Map.Strict as Map (insert, toList)

import FOL
import RPGS.Game (Game(invariant, locationNames), Loc, locations)
import RPGSolve.Config (CTX)
import RPGSolve.Logging (lg)
import RPGSolve.SMT (simplify, smtLib2, valid)

-------------------------------------------------------------------------------
-- Symbolic state
-------------------------------------------------------------------------------
newtype SymSt =
  SymSt (Map Loc Term) -- assert that all location are mapped
 deriving (Eq, Ord, Show)

invSymSt :: Game -> SymSt
invSymSt = SymSt . invariant

symSt :: Game -> (Loc -> Term) -> SymSt
symSt g gen = SymSt (fromSet gen (locations g))

get :: SymSt -> Loc -> Term
get (SymSt s) l =
  maybe (error "Assertion: All locations should be mapped") id (s !? l)

set :: SymSt -> Loc -> Term -> SymSt
set (SymSt s) l f = SymSt (Map.insert l f s)

disj :: SymSt -> Loc -> Term -> SymSt
disj s l f = set s l (orf [f, s `get` l])

disjS :: SymSt -> SymSt -> SymSt
disjS (SymSt a) b =
  SymSt (mapWithKey (\l f -> orf [f, b `get` l]) a)

differenceS :: SymSt -> SymSt -> SymSt
differenceS (SymSt a) b =
  SymSt (mapWithKey (\l f -> andf [f, neg (b `get` l)]) a)

impliesS :: SymSt -> SymSt -> IO Bool
impliesS (SymSt a) b =
  valid (andf ((\l -> ((SymSt a) `get` l) `impl` (b `get` l)) <$> keys a))

lgS :: CTX -> String -> Game -> SymSt -> IO ()
lgS ctx item g (SymSt s) =
  lg ctx item (smtLib2 <$> mapKeys (locationNames g !) s)

locsSymSt :: SymSt -> [Loc]
locsSymSt (SymSt s) = keys s

listSymSt :: SymSt -> [(Loc, Term)]
listSymSt (SymSt s) = Map.toList s

simplifySymSt :: CTX -> SymSt -> IO SymSt
simplifySymSt ctx (SymSt s) = SymSt <$> mapM (simplify ctx) s

mapSymSt :: (Term -> Term) -> SymSt -> SymSt
mapSymSt mp (SymSt s) = SymSt (fmap mp s)
