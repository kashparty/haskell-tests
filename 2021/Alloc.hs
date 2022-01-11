module Alloc where

import Data.Maybe
import Data.List

import Types
import Examples
import Data.Tuple
import Debug.Trace

------------------------------------------------------
--
-- Part I
--
count :: Eq a => a -> [a] -> Int
count x
  -- Avoids two passes
  = foldl (\c x' -> if x == x' then c + 1 else c) 0

degrees :: Eq a => Graph a -> [(a, Int)]
degrees (ns, es)
  = [(n, count n fs + count n ts) | n <- ns]
  where
    (fs, ts) = unzip es

neighbours :: Eq a => a -> Graph a -> [a]
neighbours n (_, es)
  = ([t | (f, t) <- es, f == n]) ++ ([f | (f, t) <- es, t == n])

removeNode :: Eq a => a -> Graph a -> Graph a
removeNode n (ns, es)
  = (ns', es')
  where
    ns' = filter (/= n) ns
    es' = [(f, t) | (f, t) <- es, f /= n && t /= n]

------------------------------------------------------
--
-- Part II
--
colourGraph :: (Ord a, Show a) => Int -> Graph a -> Colouring a
colourGraph _ ([], _)
  = []
colourGraph cs g
  = (n, c) : gc
  where
    ((_, n) : _) = (sort . map swap . degrees) g
    gc = colourGraph cs (removeNode n g)
    ncs = map (`lookUp` gc) (neighbours n g)
    (c : _) = ([1..cs] \\ ncs) ++ [0]

------------------------------------------------------
--
-- Part III
--
buildIdMap :: Colouring Id -> IdMap
buildIdMap gc
  = ("return", "return") : map computeId gc
  where
    computeId (v, c) = (v, if c == 0 then v else 'R' : show c)

buildArgAssignments :: [Id] -> IdMap -> [Statement]
buildArgAssignments args regs
  = map (\a -> Assign (lookUp a regs) (Var a)) args

renameExp :: Exp -> IdMap -> Exp
-- Pre: A precondition is that every variable referenced in 
-- the expression is in the idMap. 
renameExp (Var v) regs
  = Var (lookUp v regs)
renameExp (Apply op e1 e2) regs
  = Apply op (renameExp e1 regs) (renameExp e2 regs)
renameExp e _
  = e

renameBlock :: Block -> IdMap -> Block
-- Pre: A precondition is that every variable referenced in 
-- the block is in the idMap. 
renameBlock [] _
  = []
renameBlock (Assign id e : bs) regs
  | e' == Var id' = renameBlock bs regs
  | otherwise     = Assign id' e' : renameBlock bs regs
  where
    id' = lookUp id regs
    e' = renameExp e regs
renameBlock (If p t f : bs) regs
  = If p' t' f' : renameBlock bs regs
  where
    p' = renameExp p regs
    t' = renameBlock t regs
    f' = renameBlock f regs
renameBlock (While t b : bs) regs
  = While t' b' : renameBlock bs regs
  where
    t' = renameExp t regs
    b' = renameBlock b regs

renameFun :: Function -> IdMap -> Function
renameFun (f, as, b) idMap
  = (f, as, buildArgAssignments as idMap ++ renameBlock b idMap)

-----------------------------------------------------
--
-- Part IV
--
buildIG :: [[Id]] -> IG
buildIG
  = foldr buildIG' ([], [])
  where
    buildIG' :: [Id] -> IG -> IG
    buildIG' [] g
      = g
    buildIG' (id : ids) (ns, es)
      = buildIG' ids (ns', es')
      where
        ns' = [id] `union` ns
        addedEs = [(id, id') | id' <- ids]
        es' = addedEs `union` es

-----------------------------------------------------
--
-- Part V
--
liveVars :: CFG -> [[Id]]
liveVars ps
  = map (liveVars' [] []) ps
  where
    liveVars' :: CFG -> [Id] -> ((Id, [Id]), [Int]) -> [Id]
    liveVars' vs sol p@((def, use), succ)
      | p `elem` vs = sol
      | sol == sol' = sol'
      | otherwise   = liveVars' (p : vs) sol' ((def, use), succ)
      where
        succVars = foldl union [] (map (liveVars' (p : vs) [] . (ps !!)) succ)
        sol' = use `union` (succVars \\ [def])

buildCFG :: Function -> CFG
buildCFG (id, args, b)
  = buildCFG' 0 b
  where
    usedVars :: Exp -> [Id]
    usedVars (Var v)
      = [v]
    usedVars (Apply op e1 e2)
      = usedVars e1 `union` usedVars e2
    usedVars _
      = []

    buildCFG' :: Int -> Block -> CFG 
    buildCFG' _ []
      = []
    buildCFG' pnt (Assign id e : bs) 
      | id == "return" = [((id, usedVars e), [])]
      | otherwise      = ((id, usedVars e), [idx]) : restCFG
      where
        idx = pnt + 1
        restCFG = buildCFG' idx bs
    buildCFG' pnt (If p t f : bs)
      = (("_", usedVars p), [idx, idx']) : tCFG ++ fCFG ++ restCFG
      where
        idx = pnt + 1
        tCFG = buildCFG' idx t
        idx' = idx + length tCFG
        fCFG = buildCFG' idx' f
        idx'' = idx' + length fCFG
        restCFG = buildCFG' idx'' bs
    buildCFG' pnt (While t b : bs)
      = (("_", usedVars t), [idx, idx']) : bCFG' ++ restCFG
      where
        idx = pnt + 1
        bCFG = buildCFG' idx b
        ((finalId, finalVars), _) = last bCFG
        bCFG' = init bCFG ++ [((finalId, finalVars), [pnt])]
        idx' = idx + length bCFG
        restCFG = buildCFG' idx' bs