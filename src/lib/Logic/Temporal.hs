{-# LANGUAGE LambdaCase #-}

-- TODO: Streamline nameing
module Logic.Temporal where

import Data.Set (Set, unions)
import Data.Set as Set (singleton, union)

data TLBOp
  = TLUntil
  | TLWeakUntil
  | TLRelease
  deriving (Eq, Ord, Show)

data TLUOp
  = TLNext
  | TLGlobally
  | TLEventually
  deriving (Eq, Ord, Show)

data TL a
  = TLAtomic a
  | TLAnd [TL a]
  | TLOr [TL a]
  | TLNot (TL a)
  -- Temporal operators
  | TLUnaryOp TLUOp (TL a)
  | TLBinaryOp TLBOp (TL a) (TL a)
  deriving (Eq, Ord, Show)

tlAtoms :: Ord a => TL a -> Set a
tlAtoms =
  \case
    TLAtomic atom -> Set.singleton atom
    TLAnd fs -> unions (map tlAtoms fs)
    TLOr fs -> unions (map tlAtoms fs)
    TLNot f -> tlAtoms f
    TLUnaryOp _ f -> tlAtoms f
    TLBinaryOp _ f g -> tlAtoms f `Set.union` tlAtoms g

tl2ltl :: (a -> String) -> TL a -> String
tl2ltl ap2str = go
  where
    go =
      \case
        TLAtomic atom -> ap2str atom
        TLAnd fs -> nop "&" "true" (map go fs)
        TLOr fs -> nop "|" "false" (map go fs)
        TLNot f -> "(! " ++ go f ++ ")"
        TLUnaryOp op f -> "(" ++ uop2str op ++ " " ++ go f ++ ")"
        TLBinaryOp op f g ->
          "(" ++ go f ++ " " ++ bop2str op ++ " " ++ go g ++ ")"
     --
    nop _ neut [] = neut
    nop op _ (f:fr) =
      "(" ++ f ++ concatMap (\g -> " " ++ op ++ " " ++ g) fr ++ ")"

bop2str :: TLBOp -> String
bop2str =
  \case
    TLUntil -> "U"
    TLWeakUntil -> "W"
    TLRelease -> "R"

uop2str :: TLUOp -> String
uop2str =
  \case
    TLNext -> "X"
    TLGlobally -> "G"
    TLEventually -> "F"

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------
next :: TL a -> TL a
next = TLUnaryOp TLNext

globally :: TL a -> TL a
globally = TLUnaryOp TLGlobally

eventually :: TL a -> TL a
eventually = TLUnaryOp TLEventually
