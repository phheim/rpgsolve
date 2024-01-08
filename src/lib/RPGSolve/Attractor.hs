{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module RPGSolve.Attractor
  ( Ply(..)
  , opponent
  , attractor
  , attractorCache
  , attractorEx
  , cpreS
  , CacheEntry(..)
  , Cache
  ) where

-------------------------------------------------------------------------------
import Data.Map.Strict (Map, (!), findWithDefault, fromSet)
import qualified Data.Map.Strict as Map (insert, insertWith, map)

import Control.Monad (filterM, foldM, unless)
import Data.Set (Set, empty, union)
import qualified Data.Set as Set (fromList, map, toList)
import OpenList (OpenList, pop, push)
import qualified OpenList as OL (fromSet)

import FOL
import RPGS.Game
import RPGSolve.CFG
import RPGSolve.Config
import RPGSolve.Heuristics
import RPGSolve.LemmaFinding
import RPGSolve.Logging
import RPGSolve.SMT (sat, simplify, smtLib2, valid)
import RPGSolve.SymbolicState

-------------------------------------------------------------------------------
-- Enforcement Relations
-------------------------------------------------------------------------------
data Ply
  = Sys
  | Env
  deriving (Eq, Ord, Show)

opponent :: Ply -> Ply
opponent =
  \case
    Sys -> Env
    Env -> Sys

cpre :: Ply -> Game -> SymSt -> Loc -> Term
cpre p =
  case p of
    Sys -> cpreSys
    Env -> cpreEnv

cpreS :: CTX -> Ply -> Game -> SymSt -> IO SymSt
cpreS ctx p g st = simplifySymSt ctx (symSt g (cpre p g st))

cpreSys :: Game -> SymSt -> Loc -> Term
cpreSys g st l = andf [g `inv` l, forall (inputs g) (cpreST (tran g l))]
  where
    cpreST =
      \case
        TIf p tt te -> ite p (cpreST tt) (cpreST te)
        TSys upds ->
          orf [mapTermM u (andf [st `get` l, g `inv` l]) | (u, l) <- upds]

cpreEnv :: Game -> SymSt -> Loc -> Term
cpreEnv g st l = andf [g `inv` l, exists (inputs g) (cpreET (tran g l))]
  where
    cpreET =
      \case
        TIf p tt te -> ite p (cpreET tt) (cpreET te)
        TSys upds ->
          andf [mapTermM u ((g `inv` l) `impl` (st `get` l)) | (u, l) <- upds]

-------------------------------------------------------------------------------
-- Visit Counting
-------------------------------------------------------------------------------
type VisitCounter = Map Loc Word

noVisits :: Game -> VisitCounter
noVisits g = fromSet (const 0) (locations g)

visit :: Loc -> VisitCounter -> VisitCounter
visit l = Map.insertWith (+) l 1

visits :: Loc -> VisitCounter -> Word
visits = findWithDefault 0

-------------------------------------------------------------------------------
-- Loop Game
-------------------------------------------------------------------------------
-- TODO: This is still a bit different from the formal definition as it
-- creates dead-ends. We take care that they are not queried but maybe
-- this should change
loopGame :: Game -> Loc -> (Game, Loc)
loopGame g l =
  let (g', shadow) = addLocation g (locationNames g ! l ++ "'")
      oldPreds = preds g l
      g'' =
        g'
          { initial = l
          , trans = Map.map (replaceByE l shadow) (trans g')
          , predecessors =
              (Map.insert l empty . Map.insert shadow oldPreds)
                (predecessors g')
          , invariant = Map.insert shadow (g' `inv` l) (invariant g')
          }
   in (pruneUnreachables g'', shadow)

replaceByE :: Loc -> Loc -> Transition -> Transition
replaceByE src trg = h
  where
    h =
      \case
        TIf p tt te -> TIf p (h tt) (h te)
        TSys choices ->
          TSys
            ((\(upd, l) ->
                if l == src
                  then (upd, trg)
                  else (upd, l)) <$>
             choices)

-------------------------------------------------------------------------------
-- Accleration
-------------------------------------------------------------------------------
data UsedSyms =
  UsedSyms (Set Symbol) [LemSyms]

lemmaSymbols ::
     Game -> UsedSyms -> (Term, Term, Term, LemSyms, Function, UsedSyms)
lemmaSymbols g (UsedSyms allS lems) =
  let b = uniqueName "b" allS
      s = uniqueName "s" allS
      c = uniqueName "c" allS
      lSyms = LemSyms b s c
   in ( uintPred g b
      , uintPred g s
      , uintPred g c
      , lSyms
      , UnintF s
      , UsedSyms (allS `union` Set.fromList [b, s, c]) (lSyms : lems))
  where
    uintPred g f = Func (UnintF f) [Var c (ioType g ! c) | c <- outputs g]

forallC :: Game -> Term -> Term
forallC g = forall (outputs g)

existsC :: Game -> Term -> Term
existsC g = exists (outputs g)

--
-- Step relation [EX ++ CELLS]
-- Other relations [CELLS]
-- 
expandStep :: Game -> Function -> Term -> Term
expandStep g name =
  \case
    Quant q t f -> Quant q t (expandStep g name f)
    Lambda t f -> Lambda t (expandStep g name f)
    Func n args
      | n == name -> Func n ([Var c (ioType g ! c) | c <- outputs g] ++ args)
      | otherwise -> Func n (expandStep g name <$> args)
    atom -> atom

accReach ::
     Word
  -> Ply
  -> Game
  -> Loc
  -> SymSt
  -> UsedSyms
  -> (Constraint, Term, UsedSyms, CFG)
accReach depth p g l st uSym =
  let (gl, l') = loopGame g l
      (b, s, c, lSyms, sSym, uSym') = lemmaSymbols g uSym
      st' = set st l' (orf [st `get` l, s])
      -- PROG GEN {
      cfg0 = addLoc (goalCFG st) l'
      cfg1 = mapUnmapped l (PTCopyDummy lSyms PTUnmapped) cfg0
      cfg2 =
        mapUnmapped
          l'
          (PTIf (orf [st `get` l, s]) (PTJump (mapLoc cfg0 l)) PTUnmapped)
          cfg1
      -- } PROG GEN
      (consR, stAccR, uSym'', cfg) = iterAttr depth p gl st' l' uSym' cfg2
      -- quantSub f = forallC g (andf [g `inv` l, c, neg (st `get` l)] `impl` f) <- This is not strictly necessary
      quantSub f = forallC g (andf [g `inv` l, c] `impl` f)
      cons = expandStep g sSym <$> consR
      stAcc = mapSymSt (expandStep g sSym) stAccR
      cons' =
        [ forallC g (andf [g `inv` l, b] `impl` (st `get` l))
        , quantSub (stAcc `get` l)
        , quantSub (andf cons)
        ]
   in (cons', c, uSym'', cfg)

visitingThreshold :: Word
visitingThreshold = 1

iterAttr ::
     Word
  -> Ply
  -> Game
  -> SymSt
  -> Loc
  -> UsedSyms
  -> CFG
  -> (Constraint, SymSt, UsedSyms, CFG)
iterAttr depth p g st shadow =
  attr (OL.fromSet (preds g shadow)) (noVisits g) [] st
  where
    attr ::
         OpenList Loc
      -> VisitCounter
      -> Constraint
      -> SymSt
      -> UsedSyms
      -> CFG
      -> (Constraint, SymSt, UsedSyms, CFG)
    attr ol vc cons st uSym cfg =
      case pop ol of
        Nothing -> (cons, st, uSym, cfg)
        Just (l, ol')
          | visits l vc < visitingThreshold ->
            reC l ol' cons (disj st l (cpre p g st l)) uSym (addUpd st g l cfg)
          | visits l vc == visitingThreshold && depth > 0 ->
            let (consA, fA, uSymA, cfgSub) = accReach (depth - 1) p g l st uSym
                cfg' = integrate cfgSub cfg
             in reC
                  l
                  ol'
                  (cons ++ consA)
                  (set st l (orf [fA, st `get` l]))
                  uSymA
                  cfg'
          | otherwise -> attr ol' vc cons st uSym cfg
      where
        reC l ol' = attr (preds g l `push` ol') (visit l vc)

accelReach :: CTX -> Word -> Ply -> Game -> Loc -> SymSt -> IO (Term, CFG)
accelReach ctx limit p g l st = do
  lgFirst ctx "Acceleration Reach:" (locationNames g ! l)
  lgS ctx "State:" g st
  let (cons, f, UsedSyms _ syms, cfg) =
        accReach (limit2depth limit) p g l st (UsedSyms (usedSymbols g) [])
  let cons' = cons ++ [existsC g (andf [f, neg (st `get` l)])]
  let tyc = TypedCells (outputs g) (ioType g !) (boundedCells g)
  unless
    (all (null . frees) cons')
    (fail "Assertion: Constraint with free variables")
  (res, col) <- resolve ctx limit tyc cons' f syms
  cfg <-
    pure $ foldl (flip (\(l, li) -> mapCFG (replaceLemma tyc li l))) cfg col
  cfg <- pure $ removePTDummy (outputs g) col cfg
  lgLast ctx "Acceleration result:" (smtLib2 res)
  return (res, cfg)

-------------------------------------------------------------------------------
-- Caching / Hinting
-------------------------------------------------------------------------------
-- | 'CacheEntry' represents a piece of attractor computation that is assumed
-- to be true. Note that the game it refers to is  implicit and the correctness 
-- gas to be ensured by whoever provides the cache
data CacheEntry =
  CacheEntry
    { forPlayer :: Ply
    , independendCells :: Set Symbol
    , targetSt :: SymSt
    , cachedSt :: SymSt
    , involvedLocs :: Set Loc
    }
  deriving (Eq, Ord, Show)

type Cache = [CacheEntry]

-------------------------------------------------------------------------------
-- | 'applyEntry' checks if a cache entry is applicable to an intermediate
-- attractor computation step, and if it is applies it.
applyEntry :: CTX -> Game -> Ply -> CacheEntry -> SymSt -> IO SymSt
applyEntry ctx game ply cache attrSt
  | ply /= forPlayer cache = return attrSt
  | otherwise = do
    ipred <- independedPred
    -- TODO: this check should be redundant, but check this before removing it
    check <-
      allM
        (\l -> valid (andf [targ l, ipred] `impl` (attrSt `get` l)))
        (locations game)
    if check
      then let newAttrSt =
                 disjS
                   attrSt
                   (mapSymSt (\f -> andf [ipred, f]) (cachedSt cache))
            in simplifySymSt ctx newAttrSt
      else return attrSt
  where
    dependends = filter (`notElem` independendCells cache) (outputs game)
    targ l = targetSt cache `get` l
    -- This is only one choice for the independent program variables. However
    -- this seems awfully like we are computing an interpolant. Furthermore,
    -- it might be possible to use some cheaper syntactic stuff (like setting
    -- everything non-independent to "true")
    independLocPred l
      | targ l == false = return true
      | otherwise =
        simplify ctx $ forall dependends (targ l `impl` (attrSt `get` l))
    -- 
    independedPred = do
      preds <- mapM independLocPred (Set.toList (locations game))
      simplify ctx (andf preds)
   -- 
    allM p =
      foldM
        (\val elem ->
           if val
             then p elem
             else return False)
        True

-------------------------------------------------------------------------------
-- | 'applyCache' transforms an attractor state after an update on a given 
-- location based on the 'Cache'.
applyCache :: CTX -> Game -> Ply -> Cache -> SymSt -> Loc -> IO SymSt
applyCache ctx game player cache attrSt currentLoc = go attrSt cache
  where
    go symst =
      \case
        [] -> return symst
        ce:cer
          | currentLoc `notElem` involvedLocs ce -> go symst cer
          | otherwise -> do
            symst <- applyEntry ctx game player ce symst
            go symst cer

-------------------------------------------------------------------------------
-- Attractor Computation
-------------------------------------------------------------------------------
-- | 'attractorFull' does the complete attractor computation and is later used
-- for the different type of attractor computations (with/without extraction,
--  cache, ...). Note the for correctness it has to hold
--      null cache || not (generateProgram ctx)
--  Otherwise the generated program does not make any sense.
attractorFull :: CTX -> Ply -> Game -> Cache -> SymSt -> IO (SymSt, CFG)
attractorFull ctx p g cache symst = do
  nf <- Set.fromList . map fst <$> filterM (sat . snd) (listSymSt symst)
  lgFirst ctx "Attractor:" (Set.map (locationNames g !) nf)
  lgS ctx "Initial:" g symst
  (res, cfg) <-
    attr (noVisits g) (OL.fromSet (predSet g nf)) symst (goalCFG symst)
  lgS ctx "Result:" g res
  lgEnd ctx
  return (res, cfg)
  where
    attr :: VisitCounter -> OpenList Loc -> SymSt -> CFG -> IO (SymSt, CFG)
    attr vc o st cfg =
      case pop o of
        Nothing -> return (st, cfg)
        Just (l, no) -> do
          lgStart ctx
          lgMsg ctx "Attractor step"
          lg ctx "Location:" (locationNames g ! l)
          let fo = st `get` l
          lg ctx "Old:" (smtLib2 fo)
          -- Enforcable predecessor step
          fn <- simplify ctx (orf [cpre p g st l, fo])
          lg ctx "New:" (smtLib2 fn)
          let st' = set st l fn
          let vc' = visit l vc
          -- Check if this changed something in this location
          unchanged <- valid (fn `impl` fo)
          lg ctx "Subsumption:" unchanged
          if unchanged
            then rec vc' no st cfg
            else do
              cfg <- extr (addUpd st g l cfg)
              cfg <- simpCFG cfg
              -- Caching 
              (st', cached) <-
                if any ((== p) . forPlayer) cache
                  then do
                    st'' <- applyCache ctx g p cache st' l
                    cached <-
                      filterM
                        (\l -> sat (andf [st'' `get` l, neg (st' `get` l)]))
                        (locsSymSt st)
                    return (st'', cached)
                  else return (st', [])
              lg ctx "Cached:" (Set.fromList (map (locationNames g !) cached))
              -- Compute potential new locations 
              let on' = (Set.fromList cached) `push` (preds g l `push` no)
              -- Check if we accelerate
              if accelNow l fo vc' && canAccel g && null cached
                  -- Acceleration
                then do
                  lgMsg ctx "Attempt reachability acceleration"
                  (acc, cfgSub) <- accelReach ctx (visits l vc') p g l st'
                  lg ctx "Accleration formula:" (smtLib2 acc)
                  res <- simplify ctx (orf [fn, acc])
                  succ <- not <$> valid (res `impl` fn)
                  lg ctx "Accelerated:" succ
                  if succ
                      -- Acceleration succeed
                    then do
                      cfg <- extr (integrate cfgSub cfg)
                      cfg <- simpCFG cfg
                      rec vc' on' (set st' l res) cfg
                    else rec vc' on' st' cfg
                else rec vc' on' st' cfg
      where
        rec h o st cfg = do
          lgEnd ctx
          attr h o st cfg
        accelNow l fo vc =
          (g `cyclicIn` l) && (fo /= false) && visits2accel (visits l vc)
        extr cfg =
          pure $
          if generateProgram ctx
            then cfg
            else emptyCFG
        simpCFG cfg =
          if generateProgram ctx
            then process ctx cfg
            else return cfg

canAccel :: Game -> Bool
canAccel g =
  any
    (\v -> isNumber (ioType g ! v) && (v `notElem` boundedCells g))
    (outputs g)

-------------------------------------------------------------------------------
-- | 'attractor' compute the attractor for a given player, game, and symbolic
-- state
attractor :: CTX -> Ply -> Game -> SymSt -> IO SymSt
attractor ctx p g symst =
  fst <$> attractorFull (ctx {generateProgram = False}) p g [] symst

-------------------------------------------------------------------------------
-- | 'attractorCache' compute the attractor for a given player, game, 
-- and symbolic state provided with a cache that it assumes to be true for
-- this game 
attractorCache :: CTX -> Ply -> Game -> Cache -> SymSt -> IO SymSt
attractorCache ctx p g cache symst =
  fst <$> attractorFull (ctx {generateProgram = False}) p g cache symst

-------------------------------------------------------------------------------
-- | 'attractorEx' compute the attractor for a given player, game, and symbolic
-- state and does program extraction if indicated in the 'CTX'. If it does 
-- program extraction the cache is not used.
attractorEx :: CTX -> Cache -> Ply -> Game -> SymSt -> IO (SymSt, CFG)
attractorEx ctx cache p g
  | generateProgram ctx = attractorFull ctx p g []
  | otherwise = attractorFull ctx p g cache
-------------------------------------------------------------------------------
