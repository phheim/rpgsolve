{-# LANGUAGE LambdaCase #-}

--TODO: Add invariants!
module TSLT
  ( convert
  ) where

import Data.Fixed
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map (toList)

import Data.Set (Set)
import qualified Data.Set as Set (toList)

import FOL
import RPG

encConst :: Bool -> Constant -> String
encConst ugly =
  \case
    CInt n -> "i" ++ show n ++ "()"
    CReal r -> "r" ++ showFixed True (fromRational r :: Nano) ++ "()"
    CBool True
      | ugly -> "i1()"
      | otherwise -> "true"
    CBool False
      | ugly -> "i0()"
      | otherwise -> "false"

encOp :: (a -> String) -> String -> String -> [a] -> String
encOp encA op neut =
  \case
    [] -> neut
    [x] -> "(" ++ encA x ++ ")"
    x:xr -> "(" ++ encA x ++ " " ++ op ++ " " ++ encOp encA op neut xr ++ ")"

encVar :: Bool -> Symbol -> Sort -> String
encVar check v =
  \case
    SBool
      | check -> "(eq i_" ++ v ++ " i1())"
      | otherwise -> "i_" ++ v
    SInt -> "i_" ++ v
    SReal -> "r_" ++ v
    _ -> error "Not supported"

encTerm :: Bool -> Term -> String
encTerm ugly =
  \case
    QVar _ -> error "Not supported"
    Quant _ _ _ -> error "Not supported"
    Lambda _ _ -> error "Not supported"
    Var v s -> encVar True v s
    Const c -> encConst ugly c
    Func f args ->
      case f of
        UnintF _ -> error "Not supported"
        CustomF _ _ _ -> error "Not supported"
        PredefF n
          | n == "or" && not ugly -> encOp (encTerm ugly) "||" "false" args
          | n == "and" && not ugly -> encOp (encTerm ugly) "&&" "true" args
          | n == "not" && not ugly -> "(! " ++ encTerm ugly (head args) ++ ")"
          | n == "-" && length args == 1 ->
            "(sub i0() " ++ encTerm ugly (head args) ++ ")"
          | n == "+" ->
            if length args <= 2
              then op "add" args
              else "(add " ++
                   encTerm ugly (head args) ++
                   " " ++ encTerm ugly (Func (PredefF "+") (tail args)) ++ ")"
          | n == "-" -> op "sub" args
          | n == "=" -> op "eq" args
          | n == "<" -> op "lt" args
          | n == ">" -> op "gt" args
          | n == "<=" -> op "le" args
          | n == ">=" -> op "ge" args
          | n == "*" -> op "mul" args
          | otherwise -> error (n ++ " not supported yet")
  where
    op name args =
      "(" ++ name ++ concatMap ((" " ++) . encTerm ugly) args ++ ")"

encLoc :: Game -> Loc -> String
encLoc g k = "[loc  <- i" ++ show (locNumber g k) ++ "()]"

encTrans :: Game -> Transition -> String
encTrans g =
  \case
    TIf p tt tf ->
      let encP = encTerm False p
       in "(" ++
          encP ++
          " -> " ++
          encTrans g tt ++
          ") && ((! " ++ encP ++ " ) -> " ++ encTrans g tf ++ ")"
    TSys upds -> concatMap ((++ " || ") . encUpd) upds ++ "false"
  where
    encUpd (u, l) =
      "(" ++
      concatMap
        (\(v, t) ->
           "[" ++
           encVar False v (ioType g ! v) ++ " <- " ++ encTerm True t ++ "] && ")
        (Map.toList u) ++
      "X " ++ encLoc g l ++ ")"

encState :: Game -> String
encState g =
  "//-- State: " ++
  concatMap (\v -> encVar False v (ioType g ! v) ++ ", ") (outputs g) ++ "loc"

encInputs :: Game -> String
encInputs g =
  case inputs g of
    [] -> ""
    i:ir -> "//-- Inputs: " ++ encV i ++ concatMap ((", " ++) . encV) ir
  where
    encV v = encVar False v (ioType g ! v)

encGame :: Game -> String
encGame g =
  unlines $
  [encState g, encInputs g, "guarantee {", encLoc g (initial g) ++ ";"] ++
  map
    (\(l, t) -> "G (" ++ encLoc g l ++ " -> " ++ encTrans g t ++ ");")
    (Map.toList (trans g)) ++
  ["}"]

encCond :: Game -> String -> Set Loc -> String
encCond g op loc =
  let locs = Set.toList loc
   in "guarantee { " ++
      op ++ "(" ++ concatMap (\l -> encLoc g l ++ " || ") locs ++ "false);}"

convert :: Game -> WinningCondition -> String
convert g wc =
  unlines
    [ encGame g
    , case wc of
        Reachability reach -> encCond g "F" reach
        Safety safe -> encCond g "G" safe
        Buechi fset -> encCond g "G F" fset
        CoBuechi fset -> encCond g "F G" fset
        _ -> error "Not supported"
    ]
