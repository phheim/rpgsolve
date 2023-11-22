{-# LANGUAGE LambdaCase, RecordWildCards #-}

-------------------------------------------------------------------------------
module RPGSolve.Attractor where

-------------------------------------------------------------------------------
import Data.Map.Strict (Map, (!), findWithDefault, fromSet)
import qualified Data.Map.Strict as Map (insert, insertWith, map)

import Control.Monad (filterM, unless)
import Data.Set (Set, empty, union)
import qualified Data.Set as Set (fromList, map)
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
             in reC l ol' consA (set st l (orf [fA, st `get` l])) uSymA cfg'
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
-- Attractor Computation
-------------------------------------------------------------------------------
-- Assume for the extraction that the goal is already mapped
--
attractor :: CTX -> Ply -> Game -> SymSt -> IO SymSt
attractor ctx p g symst =
  fst <$> attractorEx (ctx {generateProgram = False}) p g symst

attractorEx :: CTX -> Ply -> Game -> SymSt -> IO (SymSt, CFG)
attractorEx ctx p g symst = do
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
          fn <- simplify ctx (orf [cpre p g st l, fo])
          lg ctx "New:" (smtLib2 fn)
          let st' = set st l fn
          let vc' = visit l vc
          let on' = preds g l `push` no
          unchanged <- valid (fn `impl` fo)
          lg ctx "Subsumption:" unchanged
          if unchanged
            then rec vc' no st cfg
            else do
              cfg <- extr (addUpd st g l cfg)
              cfg <- simpCFG cfg
              if accelNow l fo vc' && canAccel g
                then do
                  lgMsg ctx "Attempt reachability acceleration"
                  (acc, cfgSub) <- accelReach ctx (visits l vc') p g l st'
                  lg ctx "Accleration formula:" (smtLib2 acc)
                  res <- simplify ctx (orf [fn, acc])
                  succ <- not <$> valid (res `impl` fn)
                  lg ctx "Accelerated:" succ
                  if succ
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
