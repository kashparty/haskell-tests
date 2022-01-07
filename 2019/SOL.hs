module SOL where

import Data.List
import Data.Maybe
import Data.Tuple

import Types
import TestData

printF :: Formula -> IO()
printF
  = putStrLn . showF
  where
    showF (Var v)
      = v
    showF (Not f)
      = '!' : showF f
    showF (And f f')
      = "(" ++ showF f ++ " & " ++ showF f' ++ ")"
    showF (Or f f')
      = "(" ++ showF f ++ " | " ++ showF f' ++ ")"

--------------------------------------------------------------------------
-- Part I

-- 1 mark
lookUp :: Eq a => a -> [(a, b)] -> b
-- Pre: The item being looked up has a unique binding in the list
lookUp 
  = (fromJust . ) . lookup

-- 3 marks
vars :: Formula -> [Id]
vars 
  = sort . nub . allVars 
  where
    allVars :: Formula -> [Id]
    allVars (Var id)
      = [id]
    allVars (Not f)
      = vars f
    allVars (And l r)
      = vars l ++ vars r
    allVars (Or l r)
      = vars l ++ vars r

-- 1 mark
idMap :: Formula -> IdMap
idMap 
  = flip zip [1..] . vars 

--------------------------------------------------------------------------
-- Part II

-- An encoding of the Or distribution rules.
-- Both arguments are assumed to be in CNF, so the
-- arguments of all And nodes will also be in CNF.
distribute :: CNF -> CNF -> CNF
distribute a (And b c)
  = And (distribute a b) (distribute a c)
distribute (And a b) c
  = And (distribute a c) (distribute b c)
distribute a b
  = Or a b

-- 4 marks
toNNF :: Formula -> NNF
toNNF (Not (Not f))
  = toNNF f
toNNF (Not (And f f'))
  = Or (toNNF (Not f)) (toNNF (Not f'))
toNNF (Not (Or f f'))
  = And (toNNF (Not f)) (toNNF (Not f'))
toNNF (And f f')
  = And (toNNF f) (toNNF f')
toNNF (Or f f')
  = Or (toNNF f) (toNNF f')
toNNF f
  = f

-- 3 marks
toCNF :: Formula -> CNF
toCNF
  = toCNF' . toNNF
  where
    toCNF' :: NNF -> CNF
    toCNF' (And f f')
      = And (toCNF' f) (toCNF' f')
    toCNF' (Or f f')
      = distribute f f'
    toCNF' f
      = f

-- 4 marks
flatten :: CNF -> CNFRep
flatten f
  = flatten' f
  where
    ids = idMap f
    flatten' :: CNF -> CNFRep
    flatten' (Var id)
      = [[lookUp id ids]]
    flatten' (Not (Var id))
      = [[-(lookUp id ids)]]
    flatten' (And f f')
      = flatten' f ++ flatten' f'
    flatten' (Or f f')
      = [head (flatten' f) ++ head (flatten' f')]

--------------------------------------------------------------------------
-- Part III

-- 5 marks
propUnits :: CNFRep -> (CNFRep, [Int])
propUnits f
  | null us   = (f, [])
  | otherwise = (recF, u : recU)
  where
    us = (map head . filter ((1 ==) . length)) f
    (u : _) = us
    cDel = filter (u `notElem`) f
    lDel = map (filter (-u /=)) cDel
    (recF, recU) = propUnits lDel

-- 4 marks
dp :: CNFRep -> [[Int]]
dp f
  | null f'     = [rem]
  | any null f' = []
  | otherwise   = map (rem ++) trueRem ++ map (rem ++) falseRem
  where
    (f', rem) = propUnits f
    ((u : _) : _) = f'
    trueRem = dp ([u] : f')
    falseRem = dp ([-u] : f')

--------------------------------------------------------------------------
-- Part IV

-- Bonus 2 marks
allSat :: Formula -> [[(Id, Bool)]]
allSat f
  = concatMap intsToAss sols 
  where
    sols = (dp . flatten . toCNF) f
    ids = (map swap . idMap) f

    intsToAss :: [Int] -> [[(Id, Bool)]]
    intsToAss ids'
      = intsToAss' ids' missing
      where
        missing = filter (`notElem` map abs ids') (map fst ids)

    intsToAss' :: [Int] -> [Int] -> [[(Id, Bool)]]
    intsToAss' ids' []
      = [(sort . map intToAss) ids']
    intsToAss' ids' (m : ms)
      = intsToAss' (-m : ids') ms ++ intsToAss' (m : ids') ms

    intToAss :: Int -> (Id, Bool)
    intToAss n
      | n > 0     = (lookUp n ids, True)
      | otherwise = (lookUp (-n) ids, False)
