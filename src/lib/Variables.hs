{-# LANGUAGE LambdaCase #-}

module Variables where

import FOL

import Data.Set (Set, union)
import qualified Data.Set as Set (empty, insert, toList)

import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map (empty, insert)

data Variables =
  Variables
    { inputs :: Set Symbol
    , stateVars :: Set Symbol
    , ioTypes :: Map Symbol Sort
    }
  deriving (Eq, Ord, Show)

data Type
  = TInput Sort
  | TOutput Sort
  deriving (Eq, Ord, Show)

allVars :: Variables -> Set Symbol
allVars vars = inputs vars `union` stateVars vars

allVarL :: Variables -> [Symbol]
allVarL vars = Set.toList $ inputs vars `union` stateVars vars

empty :: Variables
empty =
  Variables {inputs = Set.empty, stateVars = Set.empty, ioTypes = Map.empty}

sortOf :: Variables -> Symbol -> Sort
sortOf vars var =
  case ioTypes vars !? var of
    Just sort -> sort
    Nothing -> error $ "tried to access not exiting variable " ++ var

typeOf :: Variables -> Symbol -> Type
typeOf vars var
  | var `elem` inputs vars = TInput (sortOf vars var)
  | otherwise = TOutput (sortOf vars var)

isInput :: Variables -> Symbol -> Bool
isInput vars var = var `elem` inputs vars

isStateVar :: Variables -> Symbol -> Bool
isStateVar vars var = var `elem` stateVars vars

inputL :: Variables -> [Symbol]
inputL = Set.toList . inputs

stateVarL :: Variables -> [Symbol]
stateVarL = Set.toList . stateVars

addInput :: Variables -> Symbol -> Sort -> Variables
addInput vars var sort
  | var `elem` allVars vars = error $ "assert: " ++ var ++ " alread exists"
  | otherwise =
    vars
      { inputs = Set.insert var (inputs vars)
      , ioTypes = Map.insert var sort (ioTypes vars)
      }

addStateVar :: Variables -> Symbol -> Sort -> Variables
addStateVar vars var sort
  | var `elem` allVars vars = error $ "assert: " ++ var ++ " alread exists"
  | otherwise =
    vars
      { stateVars = Set.insert var (stateVars vars)
      , ioTypes = Map.insert var sort (ioTypes vars)
      }

addVariable :: Variables -> Symbol -> Type -> Variables
addVariable vars var =
  \case
    TInput sort -> addInput vars var sort
    TOutput sort -> addStateVar vars var sort

forallI :: Variables -> Term -> Term
forallI vars = forAll (inputL vars)

existsI :: Variables -> Term -> Term
existsI vars = exists (inputL vars)

forallX :: Variables -> Term -> Term
forallX vars = forAll (stateVarL vars)

existsX :: Variables -> Term -> Term
existsX vars = exists (stateVarL vars)
