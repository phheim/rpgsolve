-------------------------------------------------------------------------------
-- | 
-- Module       :   Solving
--
-- 'Solving' implements the different solving techniques for the different
-- games. 
--
-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase, RecordWildCards #-}

-------------------------------------------------------------------------------
module RPGSolve.Solving
  ( solve
  ) where

-------------------------------------------------------------------------------
import Data.Map.Strict
  ( Map
  , (!)
  , (!?)
  , findWithDefault
  , fromSet
  , keys
  , mapKeys
  , mapWithKey
  )
import qualified Data.Map.Strict as Map
  ( adjust
  , empty
  , foldlWithKey
  , fromList
  , insert
  , insertWith
  , map
  , toList
  , union
  )

import Control.Monad (filterM, foldM, unless, when)
import Data.Set (Set, difference, empty, union)
import qualified Data.Set as Set (fromList, map, toList)
import OpenList (OpenList, pop, push)
import qualified OpenList as OL (fromSet)

import FOL
import RPGS.Game
import RPGSolve.Config
import RPGSolve.Heuristics
import RPGSolve.LemmaFinding
import RPGSolve.Logging
import RPGSolve.SMT (sat, simplify, smtLib2, valid)

-------------------------------------------------------------------------------
-- Symbolic state
-------------------------------------------------------------------------------
type SymSt = Map Loc Term -- assert that all location are mapped

get :: SymSt -> Loc -> Term
get s l = maybe (error "Assertion: All locations should be mapped") id (s !? l)

set :: SymSt -> Loc -> Term -> SymSt
set s l f = Map.insert l f s

disj :: SymSt -> Loc -> Term -> SymSt
disj s l f = set s l (orf [f, s `get` l])

differenceS :: SymSt -> SymSt -> SymSt
differenceS a b = mapWithKey (\l f -> andf [f, neg (b `get` l)]) a

impliesS :: SymSt -> SymSt -> IO Bool
impliesS a b = valid (andf ((\l -> (a `get` l) `impl` (b `get` l)) <$> keys a))

lgS :: CTX -> String -> Game -> SymSt -> IO ()
lgS ctx item g s = lg ctx item (smtLib2 <$> mapKeys (locationNames g !) s)

-------------------------------------------------------------------------------
-- Stub for CFG logging
-------------------------------------------------------------------------------
newtype CFGLoc =
  CFGLoc Int
  deriving (Eq, Ord, Show)

--Invariant: all in locMap have to mapped in cfgTrans!
data CFG =
  CFG
    { cfgTrans :: Map CFGLoc ProgTrans
    , cfgLocCnt :: Int
    , cfgLocInit :: CFGLoc
    , locMap :: Map Loc CFGLoc
    }

emptyCFG :: CFG
emptyCFG =
  CFG
    { cfgTrans = Map.empty
    , cfgLocCnt = 0
    , cfgLocInit = CFGLoc 0
    , locMap = Map.empty
    }

addLoc :: CFG -> Loc -> CFG
addLoc cfg@CFG {..} l =
  case locMap !? l of
    Just _ -> error "Assertion: Cannot add exisiting locations"
    Nothing ->
      cfg
        { cfgTrans = Map.insert (CFGLoc cfgLocCnt) PTUnmapped cfgTrans
        , cfgLocCnt = cfgLocCnt + 1
        , locMap = Map.insert l (CFGLoc cfgLocCnt) locMap
        }

data ProgTrans
  = PTIf Term ProgTrans ProgTrans
  | PTJump CFGLoc
  | PTUnmapped
  | PTGoal
  | PTUpdates [(Term, Map Symbol Term, CFGLoc)]
  -- PTUpdates includes READS!!!!
  -- Acceleration related stuff
  | PTCopyDummy LemSyms ProgTrans
  | PTCopy [(Symbol, Symbol)] ProgTrans

mapCFG :: (Term -> Term) -> CFG -> CFG
mapCFG m cfg = cfg {cfgTrans = fmap go (cfgTrans cfg)}
  where
    go =
      \case
        PTIf p tt tf -> PTIf (m p) (go tt) (go tf)
        PTJump cl -> PTJump cl
        PTUnmapped -> PTUnmapped
        PTGoal -> PTGoal
        PTUpdates upds -> PTUpdates $ map (\(g, u, l) -> (m g, m <$> u, l)) upds
        PTCopy assgn t -> PTCopy assgn (go t)
        PTCopyDummy l t -> PTCopyDummy l (go t)

removePTDummy :: [Symbol] -> [(LemSyms, Lemma)] -> CFG -> CFG
removePTDummy cells col cfg = cfg {cfgTrans = fmap go (cfgTrans cfg)}
  where
    mapping = Map.fromList col
    go =
      \case
        PTIf p tt tf -> PTIf p (go tt) (go tf)
        PTJump cl -> PTJump cl
        PTUnmapped -> PTUnmapped
        PTGoal -> PTGoal
        PTUpdates upds -> PTUpdates upds
        PTCopy assgn t -> PTCopy assgn (go t)
        PTCopyDummy l t ->
          case mapping !? l of
            Nothing -> error ("Assertion: " ++ show l ++ " not mapped")
            Just (Lemma _ _ _ prime) ->
              PTCopy (map (\v -> (prime ++ v, v)) cells) (go t)

mapLoc :: CFG -> Loc -> CFGLoc
mapLoc cfg l =
  case locMap cfg !? l of
    Just cl -> cl
    Nothing ->
      error ("Assertion: mapLoc expects everything to be mapped " ++ show l)

setInitialCFG :: CFG -> Loc -> CFG
setInitialCFG cfg l = cfg {cfgLocInit = mapLoc cfg l}

-- Invariant should be covered by attractor!
makeTrans :: CFG -> Game -> SymSt -> Loc -> ProgTrans
makeTrans cfg g oldAttr l = PTUpdates $ go [] (tran g l)
  where
    go cs =
      \case
        TIf p tt tf -> go (p : cs) tt ++ go (neg p : cs) tf
        TSys upds -> map (redUpds cs) upds
    redUpds cs (u, l) =
      (andf (reverse (mapTermM u (oldAttr `get` l) : cs)), u, mapLoc cfg l)

mapUnmapped :: Loc -> ProgTrans -> CFG -> CFG
mapUnmapped l pt cfg =
  cfg {cfgTrans = Map.adjust go (mapLoc cfg l) (cfgTrans cfg)}
  where
    go =
      \case
        PTUpdates upds -> PTUpdates upds
        PTIf p tt tf -> PTIf p (go tt) (go tf)
        PTJump cl -> PTJump cl
        PTUnmapped -> pt
        PTGoal -> PTGoal
        PTCopyDummy l t -> PTCopyDummy l (go t)
        PTCopy asgn t -> PTCopy asgn (go t)

addUpd :: SymSt -> Game -> Loc -> CFG -> CFG
addUpd symSt g l cfg =
  cfg {cfgTrans = Map.adjust go (mapLoc cfg l) (cfgTrans cfg)}
  where
    PTUpdates updsN = makeTrans cfg g symSt l
    go =
      \case
        PTIf p tt tf -> PTIf p (go tt) (go tf)
        PTJump cl -> PTJump cl
        PTUnmapped -> PTUpdates updsN
        PTGoal -> PTGoal
        PTCopyDummy l t -> PTCopyDummy l (go t)
        PTCopy a t -> PTCopy a (go t)
        PTUpdates upds ->
          let cond = orf $ map (\(c, _, _) -> neg c) upds
           in PTUpdates $ foldl (addUpd cond) upds updsN
    addUpd c us (g, u, l) =
      case us of
        [] -> [(g, u, l)]
        (g', u', l'):ur
          | u == u' && l == l' -> (orf [g', andf [c, g]], u, l) : ur
          | otherwise -> (g', u', l') : addUpd c ur (g, u, l)

mkCFG :: [Loc] -> CFG
mkCFG = foldl addLoc emptyCFG

-- DO NOT READ BEFORE GOAL
goalCFG :: SymSt -> CFG
goalCFG symSt =
  Map.foldlWithKey
    (\cfg l t -> mapUnmapped l (PTIf t PTGoal PTUnmapped) cfg)
    (mkCFG (keys symSt))
    symSt

mapGoal :: (Loc -> ProgTrans) -> CFG -> CFG
mapGoal m cfg =
  Map.foldlWithKey
    (\cfg l cl -> cfg {cfgTrans = Map.adjust (go l) cl (cfgTrans cfg)})
    cfg
    (locMap cfg)
  where
    go l =
      \case
        PTUpdates upds -> PTUpdates upds
        PTCopy asgn t -> PTCopy asgn (go l t)
        PTIf p tt tf -> PTIf p (go l tt) (go l tf)
        PTJump cl -> PTJump cl
        PTUnmapped -> PTUnmapped
        PTGoal -> m l
        PTCopyDummy ls t -> PTCopyDummy ls (go l t)

redirectGoal :: Game -> SymSt -> CFG -> CFG
redirectGoal g symSt cfg = mapGoal (makeTrans cfg g symSt) cfg

integrate :: CFG -> CFG -> CFG
integrate sub main =
  let sub0 = mapGoal (PTJump . mapLoc main) sub
      iSub = cfgLocCnt sub0
      iMain = cfgLocCnt main
   in CFG
        { cfgTrans =
            cfgTrans main `Map.union`
            Map.fromList
              ((\(CFGLoc i, t) -> (CFGLoc (i + iMain), go iMain t)) <$>
               Map.toList (cfgTrans sub0))
        , cfgLocCnt = iSub + iMain
        , cfgLocInit = cfgLocInit main
        , locMap = locMap main
        }
  where
    go add =
      \case
        PTIf p tt tf -> PTIf p (go add tt) (go add tf)
        PTJump (CFGLoc cl) -> PTJump (CFGLoc (cl + add))
        PTUnmapped -> PTUnmapped
        PTGoal -> PTGoal
        PTCopyDummy ls t -> PTCopyDummy ls (go add t)
        PTCopy asgn t -> PTCopy asgn (go add t)
        PTUpdates upds ->
          PTUpdates $ map (\(g, u, CFGLoc cl) -> (g, u, CFGLoc (cl + add))) upds

process :: CTX -> CFG -> IO CFG
process ctx cfg =
  foldM
    (\cfg cl -> do
       pt <- go (cfgTrans cfg ! cl)
       return cfg {cfgTrans = Map.insert cl pt (cfgTrans cfg)})
    cfg
    (keys $ cfgTrans cfg)
  where
    go =
      \case
        PTIf p tt tf -> do
          p <- simplify ctx p
          if p == true
            then go tt
            else if p == false
                   then go tf
                   else do
                     tt <- go tt
                     tf <- go tf
                     return $ PTIf p tt tf
        PTJump cl -> return $ PTJump cl
        PTUnmapped -> return PTUnmapped
        PTGoal -> return PTGoal
        PTCopyDummy ls t -> do
          t <- go t
          return $ PTCopyDummy ls t
        PTCopy asgn t -> do
          t <- go t
          return $ PTCopy asgn t
        PTUpdates upds -> do
          upds <-
            mapM
              (\(g, u, l) -> do
                 g <- simplify ctx g
                 return (g, u, l))
              upds
          return $ PTUpdates $ filter (\(g, _, _) -> g /= false) upds

printCFG :: Game -> CFG -> String
printCFG g cfg =
  unlines $
  ("read" ++ concatMap (" " ++) (outputs g) ++ ";") :
  ("goto " ++ wCFGL (cfgLocInit cfg) ++ ";") :
  map (\(cl, t) -> wCFGL cl ++ ": " ++ go t) (Map.toList (cfgTrans cfg))
  where
    wCFGL (CFGLoc i) = show i
    go =
      \case
        PTIf p tt tf ->
          "if " ++ smtLib2 p ++ " {" ++ go tt ++ "} else {" ++ go tf ++ "}"
        PTCopy assgn t ->
          "[" ++
          concatMap (\(v, t) -> " " ++ v ++ ":=" ++ t) assgn ++ " ]; " ++ go t
        PTJump cl -> "goto " ++ wCFGL cl ++ ";"
        PTUnmapped -> "abort();"
        PTGoal -> error "Assertion: Found PTGoal"
        PTCopyDummy _ _ -> error "Assertion: Found PTCopyDummy"
        PTUpdates upds ->
          "read " ++
          concatMap (" " ++) (outputs g) ++
          "; " ++
          "case {" ++
          concatMap
            (\(g, u, l) ->
               "if " ++
               smtLib2 g ++
               " [" ++
               concatMap
                 (\(v, t) -> " " ++ v ++ " := " ++ smtLib2 t)
                 (Map.toList u) ++
               "] goto " ++ wCFGL l ++ ";")
            upds ++
          "otherwise abort() };"

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
cpreS ctx p g st = mapM (simplify ctx) (fromSet (cpre p g st) (locations g))

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
      stAcc = expandStep g sSym <$> stAccR
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
  nf <- Set.fromList . map fst <$> filterM (sat . snd) (Map.toList symst)
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
-- Solving
-------------------------------------------------------------------------------
solve :: CTX -> Game -> WinningCondition -> IO ()
solve ctx g win = do
  (res, cfg) <-
    case win of
      Reachability ls -> solveReach ctx g ls
      Safety ls -> solveSafety ctx g ls
      Buechi ls -> solveBuechi ctx g ls
      CoBuechi ls -> solveCoBuechi ctx g ls
      Parity rank -> solveParity ctx g rank
  if res
    then do
      putStrLn "Realizable"
      when (generateProgram ctx) (process ctx cfg >>= putStrLn . printCFG g)
    else putStrLn "Unrealizable"

selectInv :: Game -> Set Loc -> SymSt
selectInv g locs =
  fromSet
    (\l ->
       if l `elem` locs
         then g `inv` l
         else false)
    (locations g)

solveReach :: CTX -> Game -> Set Loc -> IO (Bool, CFG)
solveReach ctx g reach = do
  lgFirst ctx "Game type:" "Reachability"
  (a, cfg) <- attractorEx ctx Sys g (selectInv g reach)
  res <- valid (a `get` initial g)
  lgLast ctx "Game result:" res
  if res && generateProgram ctx
    then do
      cfg <- pure $ redirectGoal g (invariant g) cfg
      cfg <- pure $ setInitialCFG cfg (initial g)
      return (res, cfg)
    else return (res, emptyCFG)

foldLocs :: Set Loc -> (Loc -> CFG -> CFG) -> CFG -> CFG
foldLocs locs f cfg = foldl (flip f) cfg locs

solveSafety :: CTX -> Game -> Set Loc -> IO (Bool, CFG)
solveSafety ctx g safes = do
  lgFirst ctx "Game type:" "Safety"
  let envGoal = selectInv g (locations g `difference` safes)
  a <- attractor ctx Env g envGoal
  lgS ctx "Unsafe states:" g a
  lg ctx "Initial formula:" (smtLib2 (a `get` initial g))
  res <- not <$> sat (a `get` initial g)
  lgLast ctx "Game result:" res
  if res && generateProgram ctx
    then do
      cfg <-
        pure $
        foldLocs
          (locations g)
          (addUpd (neg <$> a) g)
          (mkCFG (Set.toList (locations g)))
      cfg <- pure $ setInitialCFG cfg (initial g)
      return (res, cfg)
    else return (res, emptyCFG)

iterBuechi :: CTX -> Ply -> Game -> Set Loc -> IO (SymSt, SymSt)
iterBuechi ctx p g accept = iter (selectInv g accept) (0 :: Word)
  where
    iter fset i = do
      lg ctx "Iteration:" i
      lgS ctx "F_i" g fset
      bset <- attractor ctx p g fset
      lgS ctx "B_i" g bset
      cset <- cpreS ctx p g bset
      lgS ctx "C_i" g cset
      wset <- attractor ctx (opponent p) g (neg <$> cset)
      lgS ctx "W_i+1" g wset
      fset' <- mapM (simplify ctx) (fset `differenceS` wset)
      lgS ctx "F_i+1" g fset'
      fp <- impliesS fset fset'
      if fp
        then do
          lgS ctx "Fixed point:" g fset'
          return (wset, fset)
        else do
          lgS ctx "Recursion:" g fset'
          iter fset' (i + 1)

solveBuechi :: CTX -> Game -> Set Loc -> IO (Bool, CFG)
solveBuechi ctx g accepts = do
  lgFirst ctx "Game type:" "Buechi"
  lg ctx "Acceptings:" (Set.map (locationNames g !) accepts)
  (wenv, fset) <- iterBuechi ctx Sys g accepts
  lg ctx "Environment winning:" (smtLib2 (wenv `get` initial g))
  res <- not <$> sat (wenv `get` initial g)
  lgLast ctx "Game result:" res
  if res && generateProgram ctx
    then do
      (attr, cfg) <- attractorEx ctx Sys g fset
      cfg <- pure $ redirectGoal g attr cfg
      cfg <- pure $ setInitialCFG cfg (initial g)
      return (True, cfg)
    else return (res, emptyCFG)

solveCoBuechi :: CTX -> Game -> Set Loc -> IO (Bool, CFG)
solveCoBuechi ctx g stays = do
  lgFirst ctx "Game type:" "coBuechi"
  let rejects = locations g `difference` stays
  lg ctx "Rejects:" (Set.map (locationNames g !) rejects)
  (wsys, _) <- iterBuechi ctx Env g rejects
  lg ctx "System winning:" (smtLib2 (wsys `get` initial g))
  res <- valid (wsys `get` initial g)
  lgLast ctx "Game result:" res
  if res && generateProgram ctx
    then error "TODO"
    else return (res, emptyCFG)

solveParity :: CTX -> Game -> Map Loc Word -> IO (Bool, CFG)
solveParity = error "Old implementation was buggy, under construction."
-------------------------------------------------------------------------------
