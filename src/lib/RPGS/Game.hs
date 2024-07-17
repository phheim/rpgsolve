-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-- TODO: Make consitent with project wide connvetion: game structure -> g, ...
-- TODO: Encapsulate structure of Game completely!
-------------------------------------------------------------------------------
module RPGS.Game
  ( Loc
  , Game(initial, inputs, outputs, ioType, locationNames, invariant,
     trans, predecessors, boundedCells)
  , WinningCondition(..)
  , Transition(..)
  -- Access
  , locationCnt
  , locations
  , tran
  , inv
  , preds
  , predSet
  , locName
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
  , mapTerms
  , cyclicIn
  , usedSymbols
  , pruneUnreachables
  , locNumber
  --
  , simplifyRPG
  ) where

-------------------------------------------------------------------------------
import Data.Map.Strict
  ( Map
  , (!)
  , (!?)
  , findWithDefault
  , insertWith
  , member
  , restrictKeys
  )
import qualified Data.Map.Strict as Map
  ( elems
  , empty
  , filterWithKey
  , insert
  , toList
  )
import Data.Set
  ( Set
  , difference
  , empty
  , fromList
  , insert
  , intersection
  , singleton
  , union
  , unions
  )
import qualified Data.Set as Set (map)

import FOL (Sort, Symbol, Term(Var), andf, neg, symbols, true)
import Utils.OpenList (pop, push, pushOne)
import qualified Utils.OpenList as OL (empty)

import Config (Config)
import SMT (unsat)

import Control.Monad (liftM2)
import Data.Bifunctor (first)
import Utils.Extra (ifM, predecessorRelation)

import Data.List (nub)

-------------------------------------------------------------------------------
newtype Loc =
  Loc Word
  deriving (Eq, Ord, Show)

locNumber :: Game -> Loc -> Word
locNumber _ (Loc w) = w

data Transition
  = TIf Term Transition Transition
  -- ^ guarded branch on some quanitifer-free formula
  | TSys [(Map Symbol Term, Loc)]
  -- ^ system selection with not-empty and unique mapping
  deriving (Eq, Ord, Show)

succT :: Transition -> Set Loc
succT =
  \case
    TIf _ tt te -> succT tt `union` succT te
    TSys choices -> fromList (snd <$> choices)

mapTerms :: (Term -> Term) -> Transition -> Transition
mapTerms m =
  \case
    TIf p tt te -> TIf (m p) (mapTerms m tt) (mapTerms m te)
    TSys upds -> TSys (map (\(u, l) -> (fmap m u, l)) upds)

data WinningCondition
  = Safety (Set Loc)
  -- ^ safety winning condition with locations that should not be left
  | Reachability (Set Loc)
  -- ^ reachability winning condition with location that should be reached
  | Buechi (Set Loc)
  -- ^ Büchi winning condition with location that should be reached 
  -- infinitely often (i.e. G F set)
  | CoBuechi (Set Loc)
   -- ^ coBüchi winning condition with location that form some point on should
   -- never be left (i.e. F G set)
  | Parity (Map Loc Word)
   -- ^ Parity winning condition with coloring Omega. The system wins if the 
   -- maximal color visited infinitely often is even
  deriving (Eq, Ord, Show)

-- Loc go form 0 to cnt - 1
data Game =
  Game
    { initial :: Loc
    , cnt :: Word
    , inputs :: [Symbol]
    , outputs :: [Symbol]
    , ioType :: Map Symbol Sort
    , trans :: Map Loc Transition
    -- ^ all locations should be mapped
    , predecessors :: Map Loc (Set Loc)
    , locationNames :: Map Loc String
    , invariant :: Map Loc Term
    -- ^ all location should be mapped, default mapping to true
    -- Domain knowledge:
    , boundedCells :: [Symbol]
    }
  deriving (Show)

locationCnt :: Game -> Word
locationCnt = cnt

locName :: Game -> Loc -> String
locName g l =
  maybe (error "Assertion: Location expected") id (locationNames g !? l)

tran :: Game -> Loc -> Transition
tran g l = maybe (error "Assertion: Transition expected") id (trans g !? l)

inv :: Game -> Loc -> Term
inv g l =
  maybe
    (error "Assertion: All invariants should be mapped!")
    id
    (invariant g !? l)

setInv :: Game -> Loc -> Term -> Game
setInv g l i = g {invariant = Map.insert l i (invariant g)}

emptyGame :: Game
emptyGame =
  Game
    { initial = Loc 0
    , cnt = 0
    , inputs = []
    , outputs = []
    , ioType = Map.empty
    , trans = Map.empty
    , predecessors = Map.empty
    , locationNames = Map.empty
    , invariant = Map.empty
    , boundedCells = []
    }

sameSymbolGame :: Game -> Game
sameSymbolGame game =
  Game
    { initial = Loc 0
    , cnt = 0
    , inputs = inputs game
    , outputs = outputs game
    , ioType = ioType game
    , trans = Map.empty
    , predecessors = Map.empty
    , locationNames = Map.empty
    , invariant = Map.empty
    , boundedCells = boundedCells game
    }

locations :: Game -> Set Loc
locations g
  | cnt g > 0 = fromList (map Loc [0 .. cnt g - 1])
  | otherwise = empty

addLocation :: Game -> String -> (Game, Loc)
addLocation g name =
  ( g
      { cnt = cnt g + 1
      , locationNames = Map.insert (Loc (cnt g)) name (locationNames g)
      , invariant = Map.insert (Loc (cnt g)) true (invariant g)
      }
  , Loc (cnt g))

setInitial :: Game -> Loc -> Game
setInitial g l = g {initial = l}

addInput :: Game -> Symbol -> Sort -> Maybe Game
addInput g input sort
  | input `elem` inputs g = Nothing
  | input `elem` outputs g = Nothing
  | otherwise =
    Just $
    g {inputs = input : inputs g, ioType = Map.insert input sort (ioType g)}

addOutput :: Game -> Symbol -> Sort -> Bool -> Maybe Game
addOutput g output sort bound
  | output `elem` outputs g = Nothing
  | output `elem` inputs g = Nothing
  | otherwise =
    Just $
    g
      { outputs = output : outputs g
      , ioType = Map.insert output sort (ioType g)
      , boundedCells = [output | bound] ++ boundedCells g
      }

addTransition :: Game -> Loc -> Transition -> Maybe Game
addTransition g l t
  | l `member` trans g = Nothing
  | otherwise =
    Just $ foldl (addPred l) (g {trans = Map.insert l t (trans g)}) (succT t)
  where
    addPred pre g suc =
      g {predecessors = insertWith union suc (singleton pre) (predecessors g)}

preds :: Game -> Loc -> Set Loc
preds g l = findWithDefault empty l (predecessors g)

predSet :: Game -> Set Loc -> Set Loc
predSet g ls = unions (Set.map (preds g) ls)

succs :: Game -> Loc -> Set Loc
succs g l = maybe empty succT (trans g !? l)

cyclicIn :: Game -> Loc -> Bool
cyclicIn g start = any (elem start . reachables g) (succs g start)

reachables :: Game -> Loc -> Set Loc
reachables g l = bfs empty (l `pushOne` OL.empty)
  where
    bfs seen ol =
      case pop ol of
        Nothing -> seen
        Just (o, ol')
          | o `elem` seen -> bfs seen ol'
          | otherwise ->
            let seen' = o `insert` seen
             in bfs seen' ((succs g o `difference` seen) `push` ol')

-- TODO: this breaks the invariants
pruneUnreachables :: Game -> Game
pruneUnreachables g =
  let reach = reachables g (initial g)
   in g
        { predecessors =
            intersection reach <$> restrictKeys (predecessors g) reach
        , trans = restrictKeys (trans g) reach
        }

usedSymbols :: Game -> Set Symbol
usedSymbols g =
  fromList (inputs g) `union` fromList (outputs g) `union`
  unions (Map.elems (symTrans <$> trans g)) `union`
  unions (map (symbols . snd) (Map.toList (invariant g)))
  where
    symTrans =
      \case
        TIf p t1 t2 -> symbols p `union` symTrans t1 `union` symTrans t2
        TSys choices ->
          unions (concatMap (map (symbols . snd) . Map.toList . fst) choices)

-------------------------------------------------------------------------------
simplifyTransition :: Config -> Transition -> IO Transition
simplifyTransition cfg = go [true]
  where
    go cond =
      \case
        TSys upd -> return $ TSys $ nub $ map (first simplifyUpdates) upd
        TIf p tt tf ->
          let rectt = go (p : cond) tt
              rectf = go (neg p : cond) tf
           in ifM (unsat cfg (andf (p : cond))) rectf $
              ifM (unsat cfg (andf (neg p : cond))) rectt $
              liftM2 (TIf p) rectt rectf

simplifyUpdates :: Map Symbol Term -> Map Symbol Term
simplifyUpdates =
  Map.filterWithKey $ \var ->
    \case
      Var v _ -> v /= var
      _ -> True

--TODO: add pruning of locations. Warning this needs also to accounte possible winning conditions!
simplifyRPG :: Config -> (Game, WinningCondition) -> IO (Game, WinningCondition)
simplifyRPG cfg (game, wc) = do
  newTrans <- mapM (simplifyTransition cfg) (trans game)
  let next l = maybe (error ("assert: location not mapped " ++ show l)) id (newTrans !? l)
  return
    ( game
        { trans = newTrans
        , predecessors =
            predecessorRelation (succT . next) (locations game)
        }
    , wc)
